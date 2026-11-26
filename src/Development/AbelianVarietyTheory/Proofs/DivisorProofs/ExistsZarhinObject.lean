module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundlePrincipal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinTrickLevelSymplecticGeometricPoints

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.H2EqZeroOfIsInitial
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbelianDualCrystal.Test

section Dual

variable {S : Scheme.{0}} {A B A₁ B₁ : Over S} [GrpObj A] [GrpObj B] [GrpObj A₁] [GrpObj B₁]
  {P : LB (A ⊗ B).left} {P₁ : LB (A₁ ⊗ B₁).left}

theorem point_ext (h : IsDual A B P) {T : Over S} {x y : T ⟶ B}
    (e : evc h.isLB (fst A T) (snd A T ≫ x) = evc h.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev P (fst A T) (snd A T ≫ x)).IsLB := pull_isLB h.isLB _
  refine (h.univ T _ hM ((isAdditive_iff hM).2 fun Y a a' t ↦ ?_)).unique
    ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.additive _ _ _ _

theorem dual_unique {B' : Over S} [GrpObj B'] {P' : LB (A ⊗ B').left} (h : IsDual A B P) (h' : IsDual A B' P') :
    Nonempty (B ≅ B') := by
  have key : ∀ {C D : Over S} [GrpObj C] [GrpObj D] {Q : LB (A ⊗ C).left} {Q' : LB (A ⊗ D).left}
      (q : IsDual A C Q) (q' : IsDual A D Q'), ∃ x : C ⟶ D, ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ C),
        evc q'.isLB a (b ≫ x) = evc q.isLB a b := by
    intro C D _ _ Q Q' q q'
    obtain ⟨x, hx, -⟩ := q'.univ C Q q.isLB q.additive
    refine ⟨x, fun Y a b ↦ ?_⟩
    have := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff q.isLB (pull_isLB q'.isLB _)).2 hx)
    rw [cls_ev q'.isLB, pull_evc] at this
    simpa [evc] using this.symm
  obtain ⟨x, hx⟩ := key h h'
  obtain ⟨y, hy⟩ := key h' h
  exact ⟨⟨x, y, point_ext h (by rw [← Category.assoc, hy, hx, Category.comp_id]),
    point_ext h' (by rw [← Category.assoc, hx, hy, Category.comp_id])⟩⟩

end Dual

section Crystal

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {κ : DividedPowers I} {π : R →+* R₀}

end Crystal

end GlobalTheory.Published.AbelianDualCrystal.Test
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionDual
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.AbDual GlobalTheory.CechPic
open GlobalTheory.SerreTateDef (IsPairRed polBundle)
open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin (IsPolarisation)
open GlobalTheory.BadPt (IsWeilHom)
open GlobalTheory.PerfdLat (dualBaseChange)

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.DualTower

theorem dim_eq_of_isDual {K : Type} [Field K] (A D : AV.AbVar K) (P : LB (A.X ⊗ D.X).left)
    (h : IsDual A.X D.X P) : D.dim = A.dim := by
  obtain ⟨B, _, P₀, _, hdim, hdual, _⟩ := GlobalTheory.dualAbelianScheme _ A.X A.ab
  obtain ⟨e⟩ := GlobalTheory.Published.AbelianDualCrystal.Test.dual_unique hdual h
  have hB := hdim A.dim A.smooth
  have hne : Nonempty (Sp K) := ⟨IsLocalRing.closedPoint K⟩
  exact (GlobalTheory.relDim_unique_of_iso_grp _ hne B D.X e.hom inferInstance A.dim D.dim hB D.smooth).symm

end GlobalTheory.DualTower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationThetaEquivariance
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemeHomCompEqMulOfKer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfDualHomomorphismKernelKilled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfDualHomomorphismKernelKilled
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
open ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.DualHomSurj

theorem surjective_of_ker_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Surjective la.left := by
  intro S A B _ _ Q la d hA hB hd _ hla hd0 hk
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have : LocallyOfFiniteType (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType la.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact la.left := QuasiCompact.of_comp _ B.hom
  have hSA := GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA
  have hLQF : LocallyQuasiFinite la.left :=
    GlobalTheory.locallyQuasiFinite_of_finite_geometric_ker _ A B la hla inferInstance inferInstance
      fun Ω _ _ t => by
        have := GlobalTheory.HomExt.finite_torsion_points hSA t hd0
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ d = 1})
          (fun x => ⟨x.1, hk _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ d = 1} => z.1) e)
  haveI : IsMonHom la := hla
  refine GlobalTheory.AbLaw.MulN.surjective_of_geomFibres la fun K _ _ s => ?_
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  obtain ⟨gA, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj A) hA'
  obtain ⟨gB, hgB⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj B) hB'
  let Ak : GlobalTheory.AV.AbVar K := { X := (Over.pullback s).obj A, ab := hA', dim := gA, smooth := hgA }
  let Bk : GlobalTheory.AV.AbVar K := { X := (Over.pullback s).obj B, ab := hB', dim := gB, smooth := hgB }
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback s).map a).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst A.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst B.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (snd A B) = snd _ _ by simp]
  have hP' : (Q.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual Ak.X Bk.X (Q.pull h) := IsDual.baseChange (isGrpPullback_pullback A s)
    (isGrpPullback_pullback B s) h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have hdim : gB = gA := GlobalTheory.DualTower.dim_eq_of_isDual Ak Bk (Q.pull h) hd'
  have : LocallyQuasiFinite ((Over.pullback s).map la).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange s la)
      inferInstance
  exact (GlobalTheory.IsogenyQuasiInverse.flat_surjective_of_field _ _ gA hA' hB' hgA (hdim ▸ hgB) _).2

end GlobalTheory.DualHomSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfDualHomomorphismKernelKilledStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Surjective la.left := by
  first | (exact @GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (exact GlobalTheory.DualHomSurj.surjective_of_ker_killed) | (intros; apply GlobalTheory.DualHomSurj.surjective_of_ker_killed  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfDualHomomorphismKernelKilled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfDualHomomorphismKernelKilled
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualHomFlat

theorem geomFibre_flat (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left)
    (la : A ⟶ B) [IsMonHom la] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hd : IsDual A B P)
    [LocallyQuasiFinite la.left] (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) :
    Flat ((Over.pullback s).map la).left := by
  letI : GrpObj ((Over.pullback s).obj A) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback s).obj B) := Functor.grpObjObj
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  obtain ⟨gA, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj A) hA'
  obtain ⟨gB, hgB⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj B) hB'
  let Ak : AV.AbVar K := { X := (Over.pullback s).obj A, ab := hA', dim := gA, smooth := hgA }
  let Bk : AV.AbVar K := { X := (Over.pullback s).obj B, ab := hB', dim := gB, smooth := hgB }
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback s).map a).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst A.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst B.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (snd A B) = snd _ _ by simp]
  have hP' : (P.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual Ak.X Bk.X (P.pull h) := IsDual.baseChange (isGrpPullback_pullback A s)
    (isGrpPullback_pullback B s) h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have hdim : gB = gA := DualTower.dim_eq_of_isDual Ak Bk (P.pull h) hd'
  subst hdim
  have : LocallyQuasiFinite ((Over.pullback s).map la).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange s la)
      inferInstance
  exact (IsogenyQuasiInverse.flat_surjective_of_field _ _ gB hA' hB' hgA hgB _).1

end GlobalTheory.DualHomFlat

namespace GlobalTheory.DualHomFlat

theorem main : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left)
    (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q →
    IsDual B A (swap Q) → IsMonHom la → 0 < d →
    (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Flat la.left := by
  intro S A B _ _ Q la d hA hB hd _ hla hdpos hker
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have : LocallyOfFiniteType (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType la.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact la.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite la.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B la hla inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hdpos
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ d = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ d = 1} => z.1) e)
  have h1 : IsProper (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper la.left := IsProper.of_comp _ B.hom
  have hf : IsFinite la.left := .of_isProper_of_locallyQuasiFinite _
  exact flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S A B la inferInstance
    inferInstance inferInstance hf fun K _ _ t => geomFibre_flat S A B Q la hA hB hd K t

end GlobalTheory.DualHomFlat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfDualHomomorphismKernelKilledStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Flat la.left := by
  first | (exact @GlobalTheory.DualHomFlat.main) | (exact GlobalTheory.DualHomFlat.main) | (intros; apply GlobalTheory.DualHomFlat.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemeHomCompEqMulOfKer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualFactor

theorem factor_of_flat {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [IsCommMonObj B] (la : A ⟶ B) [IsMonHom la] [Flat la.left] [Surjective la.left]
    [QuasiCompact la.left] (d : ℕ)
    (hk : ∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) :
    ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  obtain ⟨mu, hmu⟩ := GlobalTheory.AbelianQuotient.exists_desc la (𝟙 A ^ d) (by
    intro W a b h
    rw [comp_pow, comp_pow, Category.comp_id, Category.comp_id]
    have h1 : (a / b) ≫ la = 1 := by
      rw [GrpObj.div_comp, h, div_self']
    have h2 := hk W _ h1
    rwa [div_pow, div_eq_one] at h2)
  have := FlatQuotient.epi_of_flat_surjective la
  have := FlatQuotient.epi_tensorHom la la
  refine ⟨mu, ⟨?_, ?_⟩, hmu, ?_⟩
  · have e : (η[A] : 𝟙_ (Over S) ⟶ A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [← IsMonHom.one_hom la, Category.assoc, hmu, comp_pow, Category.comp_id, e, one_pow]
  · rw [← cancel_epi (la ⊗ₘ la), ← IsMonHom.mul_hom_assoc, hmu, tensorHom_comp_tensorHom_assoc, hmu,
      comp_pow, Category.comp_id]
    have hμ : (μ[A] : A ⊗ A ⟶ A) = fst A A * snd A A := by
      rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
    rw [hμ, comp_mul, tensorHom_fst, tensorHom_snd, comp_pow, comp_pow, Category.comp_id,
      Category.comp_id, mul_pow]
  · rw [← cancel_epi la, reassoc_of% hmu, comp_pow, Category.comp_id, pow_comp, Category.id_comp]

theorem main : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  intro S A B _ _ Q la d hA hB hAB hBA hla hd hk
  have := hA.comm
  have := hB.comm
  have := hA.proper
  have := hB.proper
  have : Surjective la.left := GlobalTheory.T.surjective_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk
  have : Flat la.left := GlobalTheory.T.flat_of_dual_homomorphism_kernel_killed S A B Q la d hA hB hAB hBA hla hd hk
  have : QuasiCompact la.left := by
    have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
    exact QuasiCompact.of_comp la.left B.hom
  exact factor_of_flat A B la d hk

end GlobalTheory.DualFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemeHomCompEqMulOfKerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualAbelianScheme_hom_comp_eq_mul_of_ker : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left) (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q → IsDual B A (swap Q) → IsMonHom la → 0 < d → (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → ∃ mu : B ⟶ A, IsMonHom mu ∧ la ≫ mu = 𝟙 A ^ d ∧ mu ≫ la = 𝟙 B ^ d := by
  first | (exact @GlobalTheory.DualFactor.main) | (exact GlobalTheory.DualFactor.main) | (intros; apply GlobalTheory.DualFactor.main <;> assumption)
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinExist

section Dual

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {Q : LB (A ⊗ B).left}

theorem evc_mul_right (hQ' : IsDual B A (swap Q)) (hQ : Q.IsLB) {Y : Over S} (a : Y ⟶ A) (b b' : Y ⟶ B) :
    evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
  have e := (isAdditive_iff hQ'.isLB).1 hQ'.additive Y b b' a
  rwa [evc_swap hQ hQ'.isLB, evc_swap hQ hQ'.isLB, evc_swap hQ hQ'.isLB] at e

theorem eq_of_evc (hQ : IsDual A B Q) {T : Over S} (x y : T ⟶ B)
    (h : evc hQ.isLB (fst A T) (snd A T ≫ x) = evc hQ.isLB (fst A T) (snd A T ≫ y)) : x = y := by
  have hM : (ev Q (fst A T) (snd A T ≫ x)).IsLB := pull_isLB hQ.isLB _
  have hadd : IsAdditive (ev Q (fst A T) (snd A T ≫ x)) := by
    refine (isAdditive_iff hM).2 fun Y a a' t => ?_
    rw [evc_ev hQ.isLB, evc_ev hQ.isLB, evc_ev hQ.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hQ.isLB).1 hQ.additive Y a a' (t ≫ x)
  refine (hQ.univ T _ hM hadd).unique ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB hQ.isLB _)).1 ?_)
  rw [cls_ev hQ.isLB, cls_ev hQ.isLB]
  exact h

end Dual

section Siegel

variable {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)

theorem evc_mul_left (hA : Out.RelAmple c.A c.diag) {Y : Over S} (a a' b : Y ⟶ c.A) :
    evc c.isLB (a * a') b = evc c.isLB a b + evc c.isLB a' b :=
  GlobalTheory.PrincipalIntegral.pair_mul c GlobalTheory.SemiRigid.globalFns hA Y a a' b

theorem evc_comm {Y : Over S} (a b : Y ⟶ c.A) : evc c.isLB a b = evc c.isLB b a :=
  GlobalTheory.PrincipalIntegral.pair_comm c Y a b

theorem isAdditive_P (hA : Out.RelAmple c.A c.diag) : IsAdditive c.P :=
  (isAdditive_iff c.isLB).2 fun _ a a' b => evc_mul_left c hA a a' b

variable {B : Over S} [GrpObj B] {Q : LB (c.A ⊗ B).left}

theorem evc_la (hQ : Q.IsLB) {la : c.A ⟶ B} (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la)))
    {Y : Over S} (a b : Y ⟶ c.A) : evc c.isLB a b = evc hQ a (b ≫ la) := by
  have e := congrArg (CechPic.pull (lift a b).left) ((cls_eq_iff c.isLB (pull_isLB hQ _)).2 hla)
  rw [cls_ev hQ, pull_evc, lift_fst, lift_snd_assoc] at e
  exact e

end Siegel

end GlobalTheory.ZarhinExist

namespace GlobalTheory.ZarhinExist

section Main

variable {S : Scheme.{0}} {h M : ℕ} {t : S ⟶ Sp (cycAway M)} (c : SiegPre h M (zetaAway M) t)
variable {B : Over S} [GrpObj B] {Q : LB (c.A ⊗ B).left}

theorem isMonHom_la (hA : Out.RelAmple c.A c.diag) (hQ : IsDual c.A B Q) (hQ' : IsDual B c.A (swap Q)) {la : c.A ⟶ B}
    (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))) : IsMonHom la := by
  refine isMonHom_of_mul la fun T x y => eq_of_evc hQ _ _ ?_
  rw [← Category.assoc, ← evc_la c hQ.isLB hla, comp_mul, comp_mul, evc_mul_right hQ' hQ.isLB, ← Category.assoc,
    ← Category.assoc, ← evc_la c hQ.isLB hla, ← evc_la c hQ.isLB hla,
    evc_comm c (fst c.A T) ((snd c.A T ≫ x) * (snd c.A T ≫ y)), evc_mul_left c hA, evc_comm c _ (fst c.A T),
    evc_comm c _ (fst c.A T)]

theorem pow_eq_one_of_la {d : ℕ} (hK : SiegKerBy c d) (hQ : IsDual c.A B Q) {la : c.A ⟶ B}
    (hla : LBIso c.P (ev Q (fst c.A c.A) (snd c.A c.A ≫ la))) {T : Over S} (x : T ⟶ c.A) (hx : x ≫ la = 1) :
    x ^ d = 1 := by
  refine hK.2 T x ((cls_eq_zero_iff (pull_isLB c.isLB _)).1 ?_)
  change evc c.isLB (snd c.A T ≫ x) (fst c.A T) = 0
  rw [evc_comm c, evc_la c hQ.isLB hla, Category.assoc, hx, MonObj.comp_one, evc_one_right hQ.isLB hQ.zero]

end Main

end GlobalTheory.ZarhinExist

namespace GlobalTheory.ZarhinExist

open GlobalTheory.ZarhinFam

theorem exists_zData : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (B : Over S) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A), GlobalTheory.ZarhinFam.ZData c d B Q la mu := by
  intro h M d S t c _ _ _ hd _ _ hK
  obtain ⟨B, iB, Q, hB, -, hQ, hQ'⟩ := GlobalTheory.dualAbelianScheme S c.A c.ab
  obtain ⟨la, hla, -⟩ := hQ.univ c.A c.P c.isLB (isAdditive_P c hK.1)
  have hmon := isMonHom_la c hK.1 hQ hQ' hla
  obtain ⟨mu, hmu, h1, h2⟩ := GlobalTheory.T.exists_dualAbelianScheme_hom_comp_eq_mul_of_ker S c.A B Q la d c.ab hB hQ hQ' hmon hd
    fun T x hx => pow_eq_one_of_la c hK hQ hla x hx
  exact ⟨B, iB, hB.comm, Q, la, mu, hB, hQ, hQ', hmon, hmu, h1, h2, hla⟩

end GlobalTheory.ZarhinExist
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhin_data : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (B : Over S) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A), GlobalTheory.ZarhinFam.ZData c d B Q la mu := by
  first | (exact @GlobalTheory.ZarhinExist.exists_zData) | (exact GlobalTheory.ZarhinExist.exists_zData) | (intros; apply GlobalTheory.ZarhinExist.exists_zData <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleRigidifiedSymmetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfPowEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfPowEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomTorsionFree

open ReciprocityTheory.ChartRestriction.G.Out

theorem flat_surjective_mulA (S : Scheme.{0}) (B : Over S) [GrpObj B] (hB : IsAbelianScheme B)
    (d : ℕ) (hd : 1 ≤ d) : Flat (mulA B d).left ∧ Surjective (mulA B d).left := by
  have hc := hB.comm
  obtain ⟨hf, hfl⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S B hB d hd
  refine ⟨hfl, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_⟩
  have hfin : IsFinite ((Over.pullback t).map (mulA B d)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hf
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hfin ⊢
  have hab := TLinPf.isAb_pullback t B hB
  have := hab.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hab _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ d) hfin).2

theorem eq_of_pow_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (d : ℕ), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → ∀ (x y : B ⟶ A), IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y := by
  intro S A B _ _ _ _ _ hB d hd _ x y hx hy hxy
  obtain ⟨hfl, hsu⟩ := flat_surjective_mulA S B hB d hd
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (mulA B d)
  rw [GlobalTheory.DivisibleHom.mulA_comp, GlobalTheory.DivisibleHom.mulA_comp, hxy]

end GlobalTheory.HomTorsionFree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfPowEqStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_hom_eq_of_pow_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (d : ℕ), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → ∀ (x y : B ⟶ A), IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y := by
  first | (exact @GlobalTheory.HomTorsionFree.eq_of_pow_eq) | (exact GlobalTheory.HomTorsionFree.eq_of_pow_eq) | (intros; apply GlobalTheory.HomTorsionFree.eq_of_pow_eq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleRigidifiedSymmetric
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.ZarhinFam.Rig

section
variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem pull_pull_lift {Y W X₁ X₂ : Over S} {M : LB (X₁ ⊗ X₂).left} (hM : M.IsLB) (u : Y ⟶ W) (f : W ⟶ X₁)
    (g : W ⟶ X₂) : CechPic.pull u.left (CechPic.pull (lift f g).left (cls M hM)) = evc hM (u ≫ f) (u ≫ g) := by
  rw [← pull_comp, ← Over.comp_left, comp_lift]; rfl

theorem pull_zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (z z' : Y ⟶ Zob A B) :
    CechPic.pull (lift z z').left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (z ≫ pa A B i) (z' ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (z ≫ pa A B i) (z' ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (z' ≫ pa A B i) (z ≫ pb A B j)) +
      ∑ j, evc hQ (z' ≫ pb A B j ≫ mu) (z ≫ pb A B j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zCls, map_add (f := _), map_sum, map_zsmul, pull_pull_lift, lift_fst_assoc, lift_snd_assoc]

theorem zarhinBundle_pull_trivial_iff {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ)
    (mu : B ⟶ A) {Y : Over S} (u : Y ⟶ Zob A B ⊗ Zob A B) :
    (∃ t : ((zP A B hP hQ d mu).pull u.left).Gen, t.IsGen) ↔
      CechPic.pull u.left (zCls A B hP hQ d mu) = 0 := by
  rw [← cls_eq_zero_iff (pull_isLB (zarhinBundle_isLineBundle A B hP hQ d mu) _), cls_pull (zarhinBundle_isLineBundle A B hP hQ d mu), cls_zP]

theorem one_pa {Y : Over S} (i : Fin 4) : (1 : Y ⟶ Zob A B) ≫ pa A B i = 1 := by
  simp [pa]

theorem one_pb {Y : Over S} (j : Fin 4) : (1 : Y ⟶ Zob A B) ≫ pb A B j = 1 := by
  simp [pb]

theorem one_pb_assoc {Y X : Over S} (j : Fin 4) (f : B ⟶ X) : (1 : Y ⟶ Zob A B) ≫ pb A B j ≫ f = 1 ≫ f := by
  rw [← Category.assoc, one_pb]

end

section Sym
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem evc_symm {P : LB (A ⊗ A).left} (hP : P.IsLB) (hPs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {Y : Over S} (a a' : Y ⟶ A) : evc hP a a' = evc hP a' a := by
  have e₁ : cls P hP = evc hP (snd A A) (fst A A) := (CechPic.cls_eq_iff hP (pull_isLB hP _)).2 hPs
  change CechPic.pull (lift a a').left (cls P hP) = _
  rw [e₁, pull_evc, lift_snd, lift_fst]

theorem evc_mu_symm {P : LB (A ⊗ A).left} (hP : P.IsLB) (hPs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {Q : LB (A ⊗ B).left} (hQ : IsDual A B Q) (hQ' : IsDual B A (swap Q)) {d : ℕ} {la : A ⟶ B} {mu : B ⟶ A}
    (hmu : IsMonHom mu) (hlm : la ≫ mu = 𝟙 A ^ d) (hml : mu ≫ la = 𝟙 B ^ d)
    (hPQ : LBIso P (ev Q (fst A A) (snd A A ≫ la)))
    (htor : ∀ x y : B ⟶ A, IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y)
    {Y : Over S} (b b' : Y ⟶ B) : evc hQ.isLB (b' ≫ mu) b = evc hQ.isLB (b ≫ mu) b' := by
  have hQl := hQ.isLB
  have hs := hQ'.isLB
  have addL : ∀ (Y : Over S) (a a' : Y ⟶ A) (b : Y ⟶ B), evc hQl (a * a') b = evc hQl a b + evc hQl a' b :=
    (isAdditive_iff hQl).1 hQ.additive
  have addR : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hQl a (b * b') = evc hQl a b + evc hQl a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs).1 hQ'.additive Y b b' a
    rwa [evc_swap hQl hs, evc_swap hQl hs, evc_swap hQl hs] at k
  have powL : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ), evc hQl (a ^ n) b = n • evc hQl a b := by
    intro Y a b n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact hQ.additive.evc_one hQl b
    | succ n ih => rw [pow_succ, addL, ih, succ_nsmul]
  have powR : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ), evc hQl a (b ^ n) = n • evc hQl a b := by
    intro Y a b n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact evc_one_right hQl hQ.zero a
    | succ n ih => rw [pow_succ, addR, ih, succ_nsmul]
  have PQ : ∀ (Y : Over S) (a a' : Y ⟶ A), evc hP a a' = evc hQl a (a' ≫ la) := by
    intro Y a a'
    have e₂ : cls P hP = evc hQl (fst A A) (snd A A ≫ la) := (CechPic.cls_eq_iff hP (pull_isLB hQl _)).2 hPQ
    change CechPic.pull (lift a a').left (cls P hP) = _
    rw [e₂, pull_evc, lift_fst, lift_snd_assoc]

  let Mb : LB (B ⊗ B).left := ev Q (fst B B ≫ mu) (snd B B)
  have hM : Mb.IsLB := pull_isLB hQl _
  have evcM : ∀ (Y : Over S) (b t : Y ⟶ B), evc hM b t = evc hQl (b ≫ mu) t := by
    intro Y b t
    rw [evc_ev hQl, lift_fst_assoc, lift_snd]
  have haM : IsAdditive Mb := (isAdditive_iff hM).2 fun Y b b' t => by
    rw [evcM, evcM, evcM, MonObj.mul_comp, addL]
  obtain ⟨x, hx, -⟩ := hQ'.univ B Mb hM haM
  have K : ∀ (Y : Over S) (b t : Y ⟶ B), evc hQl (b ≫ mu) t = evc hQl (t ≫ x) b := by
    intro Y b t
    have c := (CechPic.cls_eq_iff hM (pull_isLB hs _)).2 hx
    have k : evc hM b t = evc (pull_isLB hs _) b t := congrArg (CechPic.pull (lift b t).left) c
    rw [evc_ev hs, lift_fst, lift_snd_assoc, evc_swap hQl hs, evcM] at k
    exact k
  have hss : (swap (swap Q)).IsLB := pull_isLB hs _
  have ha' : IsAdditive (swap (swap Q)) := (isAdditive_iff hss).2 fun Y a a' t => by
    simp only [evc_swap hs hss, evc_swap hQl hs]; exact addL Y a a' t
  have hsM : (swap Mb).IsLB := pull_isLB hM _
  have haSM : IsAdditive (swap Mb) := (isAdditive_iff hsM).2 fun Y t t' b => by
    simp only [evc_swap hM hsM, evcM]; exact addR Y _ t t'
  have hxm : IsMonHom x := isMonHom_of_classifying S B B A Mb (swap Q) hQ' ha' hM haSM x hx
  have key : ∀ (Y : Over S) (b : Y ⟶ B) (a : Y ⟶ A), evc hQl (a ≫ la ≫ x) b = evc hQl (a ≫ la ≫ mu) b := by
    intro Y b a
    rw [← Category.assoc a la x, ← K, ← PQ, evc_symm hP hPs, PQ, Category.assoc, hml, hlm, comp_pow,
      Category.comp_id, comp_pow, Category.comp_id, powR, powL]
  have lx : la ≫ x = la ≫ mu := by
    apply hQ'.eq_of_evc
    simpa only [evc_swap hQl hs] using key _ (fst B A) (snd B A)
  have xd : x ^ d = mu ^ d := by
    have e₁ : (𝟙 B ^ d) ≫ x = x ^ d := by rw [MonObj.pow_comp, Category.id_comp]
    have e₂ : (𝟙 B ^ d) ≫ mu = mu ^ d := by rw [MonObj.pow_comp, Category.id_comp]
    rw [← e₁, ← e₂, ← hml, Category.assoc, lx, ← Category.assoc]
  have xm : x = mu := htor x mu hxm hmu xd
  rw [K, xm]

end Sym

theorem zarhinBundle_rigidified_symmetric₂ : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B)) (fst (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B))).left) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ hdu _
  have hQ := hZ.2.1
  haveI : IsMonHom mu := hZ.2.2.2.2.1
  refine ⟨(zarhinBundle_pull_trivial_iff _ _ _ _ _ _ _).2 ?_, (zarhinBundle_pull_trivial_iff _ _ _ _ _ _ _).2 ?_, ?_⟩
  · rw [pull_zCls]
    simp only [one_pa, one_pb, one_pb_assoc, MonObj.one_comp, Category.id_comp, evc_one_left c.isLB c.rig₁,
      hQ.additive.evc_one hQ.isLB, evc_one_right hQ.isLB hQ.zero, smul_zero, Finset.sum_const_zero, add_zero]
  · rw [pull_zCls]
    simp only [one_pa, one_pb, one_pb_assoc, MonObj.one_comp, Category.id_comp, evc_one_right c.isLB c.rig₂,
      hQ.additive.evc_one hQ.isLB, evc_one_right hQ.isLB hQ.zero, smul_zero, Finset.sum_const_zero, add_zero]
  · have hz := zarhinBundle_isLineBundle c.A B c.isLB hQ.isLB d mu
    refine (CechPic.cls_eq_iff hz (pull_isLB hz _)).1 ?_
    rw [cls_pull hz, cls_zP]
    conv_lhs => rw [← pull_id (zCls _ _ _ _ _ _), ← Over.id_left, ← lift_fst_snd]
    rw [pull_zCls, pull_zCls]
    have htor : ∀ x y : B ⟶ c.A, IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y :=
      GlobalTheory.T.abelianScheme_hom_eq_of_pow_eq S c.A B c.ab hZ.1 d hd hdu
    have h1 : ∑ i, evc c.isLB (fst (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) (snd (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) =
        ∑ i, evc c.isLB (snd (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) (fst (Zob c.A B) (Zob c.A B) ≫ pa c.A B i) :=
      Finset.sum_congr rfl fun i _ => evc_symm c.isLB c.symm _ _
    have h4 : ∑ j, evc hQ.isLB (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j ≫ mu) (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) =
        ∑ j, evc hQ.isLB (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j ≫ mu) (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) :=
      Finset.sum_congr rfl fun j _ => by
        simpa only [Category.assoc] using evc_mu_symm c.isLB c.symm hQ hZ.2.2.1 hZ.2.2.2.2.1 hZ.2.2.2.2.2.1
          hZ.2.2.2.2.2.2.1 hZ.2.2.2.2.2.2.2 htor (fst (Zob c.A B) (Zob c.A B) ≫ pb c.A B j) (snd (Zob c.A B) (Zob c.A B) ≫ pb c.A B j)
    rw [h1, h4]
    abel

end GlobalTheory.ZarhinFam.Rig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleRigidifiedSymmetricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_rigidified_symmetric : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B)) (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (𝟙 (GlobalTheory.ZarhinFam.Zob c.A B)) (1 : (GlobalTheory.ZarhinFam.Zob c.A B) ⟶ (GlobalTheory.ZarhinFam.Zob c.A B))).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu) ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B)) (fst (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.Zob c.A B))).left) := by
  first | (exact @GlobalTheory.ZarhinFam.Rig.zarhinBundle_rigidified_symmetric₂) | (exact GlobalTheory.ZarhinFam.Rig.zarhinBundle_rigidified_symmetric₂) | (intros; apply GlobalTheory.ZarhinFam.Rig.zarhinBundle_rigidified_symmetric₂  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleIsomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinFamilyInclusionPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.ZarhinFam

section
variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem incZ_pa (i : Fin 4) : incZ A B ≫ pa A B i = if i = 0 then 𝟙 A else 1 := by
  unfold incZ pa mkZ
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk A _) ⟨i⟩

theorem incZ_pb (j : Fin 4) : incZ A B ≫ pb A B j = 1 := by
  unfold incZ pb mkZ
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk A _) ⟨j⟩
end

theorem zarhinBundle_pullback_inclusion : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hq0 : ∀ {Y : Over S} (a : Y ⟶ c.A), CechPic.pull (lift a (1 : Y ⟶ B)).left (cls Q hZ.2.1.isLB) = 0 :=
    fun a => evc_one_right hZ.2.1.isLB hZ.2.1.zero a
  have hp0 : ∀ {Y : Over S}, CechPic.pull (lift (1 : Y ⟶ c.A) (1 : Y ⟶ c.A)).left (cls c.P c.isLB) = 0 :=
    evc_one_left c.isLB c.rig₁ 1
  have hp1 : CechPic.pull (lift (fst c.A c.A) (snd c.A c.A)).left (cls c.P c.isLB) = cls c.P c.isLB := by
    rw [lift_fst_snd, Over.id_left, pull_id]
  refine (cls_eq_iff c.isLB (pull_isLB (zarhinBundle_isLineBundle _ _ _ _ _ _) _)).1 ?_
  rw [cls_pull (zarhinBundle_isLineBundle _ _ _ _ _ _), cls_zP]
  unfold zCls
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, tensorHom_fst_assoc,
    tensorHom_snd_assoc, incZ_pa, incZ_pb, Fin.sum_univ_four]
  simp only [MonObj.comp_one, Category.comp_id, ↓reduceIte, Fin.isValue, Fin.reduceEq, one_ne_zero, hq0, hp0, hp1, smul_zero, add_zero, zero_add, Finset.sum_const_zero]

end GlobalTheory.ZarhinFam
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_bundle_isomorphism : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  first | (exact @GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (exact GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion) | (intros; apply GlobalTheory.ZarhinFam.zarhinBundle_pullback_inclusion  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinSymplecticTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinSymplecticTransfer
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open Matrix

namespace GlobalTheory.ZarhinFam.KappaEx

def omegaB (h : ℕ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ omegaStd
    (fun a a' b => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)
    (fun a b b' => by
      simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]; congr 1; funext i; ring)
    (fun c a b => by
      simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring)

theorem omegaB_apply (h : ℕ) (a b : Fin h ⊕ Fin h → ℤ) : omegaB h a b = omegaStd a b := rfl

def emb (h : ℕ) (l : Fin 8) : Fin h ⊕ Fin h → Fin (8 * h) ⊕ Fin (8 * h) :=
  Sum.map (fun i => finProdFinEquiv (l, i)) (fun i => finProdFinEquiv (l, i))

def blk (h : ℕ) (l : Fin 8) : (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ) where
  toFun a := a ∘ emb h l
  map_zero' := rfl
  map_add' _ _ := rfl

theorem omegaStd_eq_sum_blk (h : ℕ) (a b : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    omegaStd a b = ∑ l, omegaStd (blk h l a) (blk h l b) := by
  simp only [omegaStd]
  rw [← (finProdFinEquiv (m := 8) (n := h)).sum_comp, Fintype.sum_prod_type]
  rfl

def vMat (d : ℕ) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ := fromBlocks 1 (-(quat d)ᵀ) 0 1

theorem vMat_transpose_mul_form_mul {d : ℕ} (hd : 0 < d) : (vMat d)ᵀ * form d * vMat d = 1 := by
  have h1 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
  rw [vMat, form, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> simp [Matrix.mul_neg, Matrix.neg_mul, quat_mul_transpose, h1, sub_smul]

theorem sum_sig {β : Type} [AddCommMonoid β] (g : Fin 4 ⊕ Fin 4 → β) : ∑ k, g (sig k) = ∑ s, g s := by
  simp [Fin.sum_univ_succ, Fintype.sum_sum_type, sig, add_assoc]

theorem sig_injective : Function.Injective sig := by
  intro k l hkl
  fin_cases k <;> fin_cases l <;> simp_all [sig]

def kap (h d : ℕ) (k : Fin 8) : (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ) :=
  ∑ l, vMat d (sig k) (sig l) • blk h l

theorem kap_apply (h d : ℕ) (k : Fin 8) (a : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    kap h d k a = ∑ l, vMat d (sig k) (sig l) • blk h l a := by
  simp [kap]

theorem inner_sum (d : ℕ) (m n : Fin 8) :
    ∑ k, ∑ l, vMat d (sig k) (sig m) * form d (sig k) (sig l) * vMat d (sig l) (sig n) =
      ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) := by
  have e1 : ∑ k, ∑ l, vMat d (sig k) (sig m) * form d (sig k) (sig l) * vMat d (sig l) (sig n) =
      ∑ p, ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n) :=
    sum_sig (fun p => ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n))
  have e2 : ∀ p, ∑ l, vMat d p (sig m) * form d p (sig l) * vMat d (sig l) (sig n) =
      ∑ q, vMat d p (sig m) * form d p q * vMat d q (sig n) :=
    fun p => sum_sig (fun q => vMat d p (sig m) * form d p q * vMat d q (sig n))
  rw [e1, Finset.sum_congr rfl fun p _ => e2 p]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem formZ_kap {h d : ℕ} (hd : 0 < d) (a b : Fin (8 * h) ⊕ Fin (8 * h) → ℤ) :
    formZ d h (fun k => kap h d k a) (fun k => kap h d k b) = omegaStd a b := by
  have e2 : ∀ k l, omegaStd (kap h d k a) (kap h d l b) =
      ∑ m, ∑ n, vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b) := by
    intro k l
    rw [← omegaB_apply, kap_apply, kap_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      omegaB_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  simp only [formZ, e2, Finset.mul_sum]
  have e3 : ∀ m n, ∑ k, ∑ l, form d (sig k) (sig l) *
      (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) =
      ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) * omegaStd (blk h m a) (blk h n b) := by
    intro m n
    rw [← inner_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  calc ∑ k, ∑ l, ∑ m, ∑ n, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b))
      = ∑ k, ∑ m, ∑ n, ∑ l, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ∑ k, ∑ l, form d (sig k) (sig l) *
        (vMat d (sig k) (sig m) * vMat d (sig l) (sig n) * omegaStd (blk h m a) (blk h n b)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ m, ∑ n, ((vMat d)ᵀ * form d * vMat d) (sig m) (sig n) * omegaStd (blk h m a) (blk h n b) := by
        simp only [e3]
    _ = omegaStd a b := by
        rw [vMat_transpose_mul_form_mul hd, omegaStd_eq_sum_blk]
        simp [Matrix.one_apply, sig_injective.eq_iff]

theorem blk_jlMap (h : ℕ) (l : Fin 8) (a : Fin h ⊕ Fin h → ℤ) :
    blk h l (jlMap h a) = if l = 0 then a else 0 := by
  funext x
  split_ifs with hl
  · subst hl
    rcases x with i | i <;> simp [blk, emb, jlMap]
  · have hl1 : 1 ≤ (l : ℕ) := Nat.one_le_iff_ne_zero.mpr fun h0 => hl (Fin.ext h0)
    rcases x with i | i <;> simp only [blk, emb, jlMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply,
      Sum.map_inl, Sum.map_inr, Pi.zero_apply] <;> rw [dite_eq_right] <;> simp only [finProdFinEquiv_apply_val, not_lt] <;>
      nlinarith [i.2]

theorem kap_jlMap (h d : ℕ) (k : Fin 8) (a : Fin h ⊕ Fin h → ℤ) :
    kap h d k (jlMap h a) = if k = 0 then a else 0 := by
  rw [kap_apply]
  simp only [blk_jlMap, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  fin_cases k <;> simp [vMat, sig]

end GlobalTheory.ZarhinFam.KappaEx

namespace GlobalTheory.ZarhinFam


open KappaEx in
theorem exists_kappaOK : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d →
    ∃ κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.KappaOK h M d κ := by
  intro h M d _ _ _ hd _
  refine ⟨kap h d, fun a b => ?_, fun a => ?_, fun k hk a => ?_⟩
  · rw [formZ_kap hd]
  · rw [kap_jlMap, if_pos rfl]
  · rw [kap_jlMap, if_neg hk]

end GlobalTheory.ZarhinFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinSymplecticTransferStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhinSymplecticTransfer : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ), GlobalTheory.ZarhinFam.KappaOK h M d κ := by
  first | (exact @GlobalTheory.ZarhinFam.exists_kappaOK) | (exact GlobalTheory.ZarhinFam.exists_kappaOK) | (intros; apply GlobalTheory.ZarhinFam.exists_kappaOK  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinObject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinFam

theorem exists_zarhin_object : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  intro h M d h1 hM hodd hd hcop
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_zarhinSymplecticTransfer h M d h1 hM hodd hd hcop
  refine ⟨GlobalTheory.ZarhinFam.jlMap h, 8, GlobalTheory.ZarhinFam.oMat d, κ, fun S t c hdu hk => ?_⟩
  obtain ⟨B, _, _, Q, la, mu, hZ⟩ := GlobalTheory.T.exists_zarhin_data h M d S t c h1 hM hodd hd hcop hdu hk
  obtain ⟨r1, r2, sy⟩ := GlobalTheory.T.zarhinBundle_rigidified_symmetric h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk
  obtain ⟨la1, la2⟩ := GlobalTheory.T.zarhinLevel_additive_killed_by_level h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  have hab : IsAbelianScheme (GlobalTheory.ZarhinFam.Zob c.A B) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ (AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 3)
      (AbelianSchemeGerms.isAbelianScheme_powObj B hZ.1 3)
  let z : SiegPre (8 * h) M (zetaAway M) t :=
    { A := GlobalTheory.ZarhinFam.Zob c.A B
      ab := hab
      P := GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu
      isLB := GlobalTheory.ZarhinFam.zarhinBundle_isLineBundle c.A B c.isLB hZ.2.1.isLB d mu
      rig₁ := r1
      rig₂ := r2
      symm := sy
      lev := GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ
      lev_add := la1
      lev_tors := la2
      geom := GlobalTheory.T.zarhinTrick_level_symplectic_geometricPoints h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ }
  obtain ⟨i1, i2, i3, i4, i5⟩ := GlobalTheory.T.zarhinProduct_relation_algebraic_clauses h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk κ hκ
  refine ⟨z, GlobalTheory.ZarhinFam.actZ c.A B d la mu, GlobalTheory.T.zarhinBundle_principal h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.T.zarhinOrder_isRingAction_on_product h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, GlobalTheory.T.zarhinOrderAction_rosati_adjoint h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk,
    GlobalTheory.ZarhinFam.incZ c.A B, GlobalTheory.ZarhinFam.prZ c.A B, i1, i2, i3, i4,
    GlobalTheory.T.zarhin_bundle_isomorphism h M d S t c B Q la mu hZ h1 hM hodd hd hcop hdu hk, i5, fun a => rfl⟩

end GlobalTheory.ZarhinFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinObjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  first | (exact @GlobalTheory.ZarhinFam.exists_zarhin_object) | (exact GlobalTheory.ZarhinFam.exists_zarhin_object) | (intros; apply GlobalTheory.ZarhinFam.exists_zarhin_object  <;> assumption)
end
