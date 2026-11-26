module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsPullbackPrescribed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenDomainWeightBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFpqcDesc

open GlobalTheory.SiegPBDescent GlobalTheory.SiegelPullComp

variable {h n : ℕ} {B B' B₁ : Type} [CommRing B] [CommRing B'] [CommRing B₁] {ζ' : B'} {ζ₁ : B₁}
  {T T₁ : Scheme.{0}} {s₁ : T₁ ⟶ Sp B₁}

theorem siegPB_id_of_fpqc (b : TBase B n) {sc : T ⟶ Sp B'} {su : T ⟶ Sp B} (c : SiegPre h n ζ' sc)
    (u : SiegPre h n (b.ζ : B) su) (c₁ : SiegPre h n ζ₁ s₁) (p : T₁ ⟶ T) [Flat p] [QuasiCompact p] [Surjective p]
    (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal) (m : SiegPB c₁ c p) (k : SiegPB c₁ u p) : SiegPB c u (𝟙 T) := by
  obtain ⟨φ₁, hm⟩ := exists_of_siegPB m
  obtain ⟨ψ₁, hk⟩ := exists_of_siegPB k
  obtain ⟨φ₁₂, hφ, sq₁, iso₁, lev₁⟩ := (sRelBy_one_iff _ _ _ _).1 hm
  obtain ⟨ψ₁₂, hψ, sq₂, iso₂, lev₂⟩ := (sRelBy_one_iff _ _ _ _).1 hk
  have : Epi p := Flat.epi_of_flat_of_surjective p
  have : Flat φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : Surjective φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : QuasiCompact φ₁ := MorphismProperty.of_isPullback hφ.1.flip inferInstance
  have : Flat ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : Surjective ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : QuasiCompact ψ₁ := MorphismProperty.of_isPullback hψ.1.flip inferInstance
  have : EffectiveEpi φ₁ := inferInstance
  have : EffectiveEpi ψ₁ := inferInstance
  let φ := EffectiveEpi.desc φ₁ ψ₁ (comp_eq_of_comp_eq b hn ho hu hm hk)
  have hφψ : φ₁ ≫ φ = ψ₁ := EffectiveEpi.fac _ _ _
  have w : φ ≫ u.A.hom = c.A.hom := by
    rw [← cancel_epi φ₁, ← Category.assoc, hφψ, hψ.1.w, hφ.1.w]
  have : Mono φ := mono_of_fac hφ.1 hψ.1 hφψ w
  let ψ := EffectiveEpi.desc ψ₁ φ₁ (fun g₁ g₂ e => by
    rw [← cancel_mono φ, Category.assoc, Category.assoc, hφψ]; exact e)
  have hψφ : ψ₁ ≫ ψ = φ₁ := EffectiveEpi.fac _ _ _
  have : IsIso φ := ⟨ψ, by rw [← cancel_epi φ₁, ← Category.assoc, hφψ, hψφ, Category.comp_id],
    by rw [← cancel_epi ψ₁, ← Category.assoc, hψφ, hφψ, Category.comp_id]⟩
  have gp : IsGrpPullback c.A u.A (𝟙 T) φ :=
    GlobalTheory.ObjDescent.isGrpPullback_id hφ hψ φ hφψ (w.trans (Category.comp_id _).symm)
  obtain ⟨φ₂, sq⟩ := GlobalTheory.SiegDesc.exists_isSquare gp.1.w
  have lev : ∀ a, (c.lev a).left ≫ φ = 𝟙 T ≫ (u.lev a).left := fun a => by
    rw [Category.id_comp, ← cancel_epi p, ← Category.assoc, ← lev₁ a, Category.assoc, hφψ, lev₂ a]
  have he : eSec (G2 c.A) ≫ φ₂ = eSec (G2 u.A) := by
    have e₀ : eSec c.A ≫ φ = 𝟙 _ ≫ eSec u.A := (cubeMapOf gp).e_comm
    rw [Category.id_comp] at e₀
    apply pullback.hom_ext
    · show (eSec (G2 c.A) ≫ φ₂) ≫ (fst u.A u.A).left = eSec (G2 u.A) ≫ (fst u.A u.A).left
      rw [Category.assoc, sq.1, ← Category.assoc, eSec_fst, eSec_fst, e₀]
    · show (eSec (G2 c.A) ≫ φ₂) ≫ (snd u.A u.A).left = eSec (G2 u.A) ≫ (snd u.A u.A).left
      rw [Category.assoc, sq.2, ← Category.assoc, eSec_snd, eSec_snd, e₀]
  have hiso : LBIso c.P (u.P.pull φ₂) := by
    have h₁ := c.isLB
    have h₂ := pull_isLB u.isLB φ₂
    have hN := LB.isLB_div h₂ h₁
    have cN : CechPic.cls _ hN = CechPic.pull φ₂ (CechPic.cls _ u.isLB) - CechPic.cls _ h₁ :=
      CechPic.cls_div h₂ h₁ hN
    have hsq := GlobalTheory.SiegDesc.isPullback_of_isSquare hφ.1 sq₁
    have e₂ : φ₁₂ ≫ φ₂ = ψ₁₂ := GlobalTheory.SiegDesc.isSquare_comp hφψ sq₁ sq sq₂
    have cl₁ : CechPic.cls c₁.P c₁.isLB = CechPic.pull φ₁₂ (CechPic.cls c.P c.isLB) :=
      (CechPic.cls_eq_iff _ (pull_isLB c.isLB _)).2 iso₁
    have cl₂ : CechPic.cls c₁.P c₁.isLB = CechPic.pull ψ₁₂ (CechPic.cls u.P u.isLB) :=
      (CechPic.cls_eq_iff _ (pull_isLB u.isLB _)).2 iso₂
    refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.abelianSchemeLaws_all.1.globalFns T T₁ p (G2 c.A) _
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ c.ab c.ab) hN inferInstance inferInstance inferInstance
      ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_) ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    · have cls_eSec {R : Type} [CommRing R] {ζ : R} {S : Scheme.{0}} {s : S ⟶ Sp R}
          (v : SiegPre h n ζ s) : CechPic.pull (eSec (G2 v.A)) (CechPic.cls v.P v.isLB) = 0 := by
        obtain ⟨t, ht⟩ := v.rig₁
        have z := (CechPic.cls_eq_zero_iff (pull_isLB v.isLB _)).2 ⟨t, ht⟩
        rw [CechPic.cls_pull v.isLB] at z
        rw [← eSec_sq, CechPic.pull_comp, z, map_zero]
      rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, he, cls_eSec u, cls_eSec c, sub_zero]
    · rw [CechPic.cls_pull hN, cN, ← hsq.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp, e₂,
        ← cl₂, ← cl₁, sub_self, map_zero]
  exact siegPB_of ((sRelBy_one_iff _ _ _ _).2 ⟨φ₂, gp, sq, hiso, lev⟩)

theorem siegPB_of_fpqc_cover (h n : ℕ) (B : Type) [CommRing B] (b : TBase B n) (S S₁ Y : Scheme.{0})
    (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (sY : Y ⟶ Sp B) (c : SiegPre h n (b.ζ : B) s) (c₁ : SiegPre h n (b.ζ : B) s₁)
    (u : SiegPre h n (b.ζ : B) sY) (p : S₁ ⟶ S) (f : S ⟶ Y) (hn : 3 ≤ n) (ho : Odd n) (hu : u.Principal)
    [Flat p] [QuasiCompact p] [Surjective p] (m : SiegPB c₁ c p) (k : SiegPB c₁ u (p ≫ f)) : SiegPB c u f := by
  obtain ⟨⟨u', hu'⟩, hpr⟩ := GlobalTheory.siegPre_pullback h n B (b.ζ : B) Y S sY (f ≫ sY) f u rfl
  have k' : SiegPB c₁ u' p := pb_cancel hu' k
  have e := pb_comp hu' (siegPB_id_of_fpqc b c u' c₁ p hn ho (hpr u' hu' hu) m k')
  rwa [Category.id_comp] at e

theorem classified_of_faithfullyFlat : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R R').comp β)), SiegPB c' c (spMap (algebraMap R R')) → ∃ f : Sp R' ⟶ F.X, f ≫ F.s = spMap ((algebraMap R R').comp β) ∧ SiegPB c' F.univ f) → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  intro g n hg hn ho F R R' _ _ _ _ β c _ H
  have hn0 : n ≠ 0 := by omega
  let π : Sp R' ⟶ Sp R := spMap (algebraMap R R')
  have : Flat π := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective π := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have : QuasiCompact π := inferInstance
  have hcomp : π ≫ spMap β = spMap ((algebraMap R R').comp β) := by
    simp only [π, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp R) (Sp R') (spMap β)
    (spMap ((algebraMap R R').comp β)) π c hcomp
  obtain ⟨f', hf's, hf'⟩ := H c' hc'
  have hagree : pullback.fst π π ≫ f' = pullback.snd π π ≫ f' := by
    obtain ⟨⟨c₁, hc₁⟩, -⟩ := GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) (Sp R') (pullback π π)
      (spMap ((algebraMap R R').comp β)) (pullback.fst π π ≫ spMap ((algebraMap R R').comp β))
      (pullback.fst π π) c' rfl
    have a₁ : SiegPB c₁ F.univ (pullback.fst π π ≫ f') := pb_comp hf' hc₁
    have b₁ : SiegPB c₁ c (pullback.fst π π ≫ π) := pb_comp hc' hc₁
    rw [pullback.condition] at b₁
    have b₂ : SiegPB c₁ c' (pullback.snd π π) := pb_cancel hc' b₁
    have a₂ : SiegPB c₁ F.univ (pullback.snd π π ≫ f') := pb_comp hf' b₂
    refine GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn ho F _ _ c₁ _ _ (by rw [Category.assoc, hf's]) ?_ a₁ a₂
    rw [Category.assoc, hf's, ← hcomp, ← Category.assoc, ← pullback.condition, Category.assoc]
  have : IsRegularEpi π := isRegularEpi_of_flat_of_surjective_of_isAffine π
  let f := EffectiveEpi.desc π f' (fun g₁ g₂ e => by
    have := congrArg (pullback.lift g₁ g₂ e ≫ ·) hagree
    rwa [← Category.assoc, ← Category.assoc, pullback.lift_fst, pullback.lift_snd] at this)
  have hf : π ≫ f = f' := EffectiveEpi.fac _ _ _
  have : Epi π := Flat.epi_of_flat_of_surjective π
  refine ⟨f, ?_, ?_⟩
  · rw [← cancel_epi π, ← Category.assoc, hf, hf's, hcomp]
  · exact siegPB_of_fpqc_cover g n (cycAway n) (cycBase hn0) (Sp R) (Sp R') F.X (spMap β) _ F.s c c' F.univ π f
      hn ho F.princ hc' (by rw [hf]; exact hf')

end GlobalTheory.SiegFpqcDesc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifiedOfFaithfullyFlatStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_classified_of_faithfullyFlat : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R R').comp β)), SiegPB c' c (spMap (algebraMap R R')) → ∃ f : Sp R' ⟶ F.X, f ≫ F.s = spMap ((algebraMap R R').comp β) ∧ SiegPB c' F.univ f) → ∃ f : Sp R ⟶ F.X, f ≫ F.s = spMap β ∧ SiegPB c F.univ f := by
  first | exact @GlobalTheory.SiegFpqcDesc.classified_of_faithfullyFlat | exact GlobalTheory.SiegFpqcDesc.classified_of_faithfullyFlat | (intros; apply GlobalTheory.SiegFpqcDesc.classified_of_faithfullyFlat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeSumGeneratorsEqOfCommonInteriorPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeSumGeneratorsEqOfCommonInteriorPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

open GlobalTheory.Poinc

theorem cone_gen_mem_of_common {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {r r' : ℕ} {ζ : Fin r → LinearMap.BilinForm ℤ X}
    {ζ' : Fin r' → LinearMap.BilinForm ℤ X} (hζ : IsCone bar φ ζ) (hζ' : IsCone bar φ ζ') (c : Fin r → ℕ)
    (c' : Fin r' → ℕ) (hc : ∀ j, 0 < c j) (he : ∑ j, c j • ζ j = ∑ j, c' j • ζ' j) (j : Fin r) :
    ∃ j', ζ j = ζ' j' := by
  obtain ⟨k, d, hk, hd⟩ := intCone_absorb hζ.mem hζ.nonneg hζ.linear hζ' c c' he j (hc j)
  have hd' : ∑ i, d i • ζ' i = ∑ l, (Pi.single j k : Fin r → ℕ) l • ζ l := by
    rw [← hd, Finset.sum_eq_single j (fun l _ hl => by simp [Pi.single_apply, hl]) (by simp)]
    simp
  have habs : ∀ i, 0 < d i → ∃ (k' : ℕ) (e : Fin r → ℕ), 0 < k' ∧ k' • ζ' i = ∑ l, e l • ζ l :=
    fun i hi => intCone_absorb hζ'.mem hζ'.nonneg hζ'.linear hζ d _ hd' i hi
  obtain ⟨f, hf⟩ := hζ.basis.exists_dual
  obtain ⟨g, hg⟩ := hζ'.basis.exists_dual
  let G : Fin r → balForms bar X := fun l => ⟨ζ l, hζ.mem l⟩
  let G' : Fin r' → balForms bar X := fun i => ⟨ζ' i, hζ'.mem i⟩
  have hfG : ∀ l m, f l (G m) = if l = m then 1 else 0 := hf
  have hgG : ∀ i m, g i (G' m) = if i = m then 1 else 0 := hg
  have hdG : k • G j = ∑ i, d i • G' i := Subtype.ext (by simp [G, G', hd])
  have hpos : ∀ i, 0 < d i → ∀ l, 0 ≤ f l (G' i) := by
    intro i hi l
    obtain ⟨k', e, hk', he'⟩ := habs i hi
    have h0 : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
    have h1 := congrArg (f l) h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      _root_.mul_one] at h1
    have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
    by_contra hneg
    push_neg at hneg
    have : (k' : ℤ) * f l (G' i) < 0 := mul_neg_of_pos_of_neg hk'' hneg
    linarith [Int.natCast_nonneg (e l)]
  have hex : ∃ i, 0 < d i := by
    by_contra hno
    push_neg at hno
    have h0 : k • ζ j = 0 := by
      rw [hd]
      exact Finset.sum_eq_zero fun i _ => by rw [Nat.le_zero.1 (hno i), zero_smul]
    refine hζ.linearIndependent.ne_zero j (LinearMap.ext₂ fun x y => ?_)
    have h1 := LinearMap.congr_fun₂ h0 x y
    simp only [LinearMap.smul_apply, LinearMap.zero_apply, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hk.ne')
    · simpa using h2
  obtain ⟨i, hi⟩ := hex
  have hzero : ∀ l, l ≠ j → f l (G' i) = 0 := by
    intro l hl
    have h1 := congrArg (f l) hdG
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum, hfG, if_neg hl, smul_zero] at h1
    simp only [map_nsmul, nsmul_eq_mul] at h1
    have hnn : ∀ i' ∈ Finset.univ, 0 ≤ (d i' : ℤ) * f l (G' i') := fun i' _ => by
      rcases Nat.eq_zero_or_pos (d i') with h | h
      · simp [h]
      · exact mul_nonneg (Int.natCast_nonneg _) (hpos i' h l)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h1.symm i (Finset.mem_univ _)
    exact (mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hi.ne')
  obtain ⟨k', e, hk', he'⟩ := habs i hi
  have hE : k' • G' i = ∑ m, e m • G m := Subtype.ext (by simp [G, G', he'])
  have hem : ∀ m, (e m : ℤ) = k' * f m (G' i) := by
    intro m
    have h1 := congrArg (f m) hE
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_sum] at h1
    simp only [map_nsmul, hfG, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul,
      _root_.mul_one] at h1
    exact h1.symm
  have hEj : k' • G' i = e j • G j := by
    rw [hE]
    refine Finset.sum_eq_single j (fun m _ hm => ?_) (by simp)
    have h1 := hem m
    rw [hzero m hm, mul_zero] at h1
    rw [show e m = 0 by exact_mod_cast h1, zero_smul]
  have h1 := congrArg (g i) hEj
  simp only [map_nsmul, hgG, if_true, nsmul_eq_mul, _root_.mul_one] at h1
  have h2 := hem j
  have hk'' : (0 : ℤ) < k' := by exact_mod_cast hk'
  have hu : f j (G' i) * g i (G j) = 1 := by
    have h3 : (k' : ℤ) * (f j (G' i) * g i (G j) - 1) = 0 := by
      rw [mul_sub, ← _root_.mul_assoc, ← h2, _root_.mul_one]
      linarith
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hk''.ne')
  have hf1 : f j (G' i) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hu with h | h
    · exact h
    · have := Int.natCast_nonneg (e j)
      rw [h2, h] at this
      linarith
  have hej : e j = k' := by
    have := h2
    rw [hf1, _root_.mul_one] at this
    exact_mod_cast this
  rw [hej] at hEj
  refine ⟨i, LinearMap.ext₂ fun x y => ?_⟩
  have h3 := LinearMap.congr_fun₂ (congrArg Subtype.val hEj) x y
  simp only [G, G', Submodule.coe_smul, LinearMap.smul_apply, nsmul_eq_mul] at h3
  exact (mul_left_cancel₀ (by exact_mod_cast hk'.ne' : (k' : ℤ) ≠ 0) h3).symm

theorem coneSum_eq : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m m' : ℕ)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (δ' : Fin m' → LinearMap.BilinForm ℤ X), IsCone id φ δ → IsCone id φ δ' →
    ∀ (c : Fin m → ℕ) (c' : Fin m' → ℕ), (∀ k, 0 < c k) → (∀ k, 0 < c' k) →
    ∑ k, c k • δ k = ∑ k, c' k • δ' k → ∑ k, δ k = ∑ k, δ' k := by
  intro φ X _ _ m m' δ δ' hδ hδ' c c' hc hc' he
  classical
  have h1 : ∀ k, ∃ j, δ k = δ' j := cone_gen_mem_of_common hδ hδ' c c' hc he
  have h2 : ∀ j, ∃ k, δ' j = δ k := cone_gen_mem_of_common hδ' hδ c' c hc' he.symm
  have himg : Finset.univ.image δ = Finset.univ.image δ' := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨j, hj⟩ := h1 k
      exact ⟨j, hj.symm⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨k, hk⟩ := h2 j
      exact ⟨k, hk.symm⟩
  have e1 : ∑ x ∈ Finset.univ.image δ, x = ∑ k, δ k :=
    Finset.sum_image fun a _ b _ h => hδ.injective h
  have e2 : ∑ x ∈ Finset.univ.image δ', x = ∑ k, δ' k :=
    Finset.sum_image fun a _ b _ h => hδ'.injective h
  rw [← e1, ← e2, himg]

end GlobalTheory.TInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothConeSumGeneratorsEqOfCommonInteriorPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothCone_sum_generators_eq_of_common_interiorPoint : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (m m' : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (δ' : Fin m' → LinearMap.BilinForm ℤ X), IsCone id φ δ → IsCone id φ δ' → ∀ (c : Fin m → ℕ) (c' : Fin m' → ℕ), (∀ k, 0 < c k) → (∀ k, 0 < c' k) → ∑ k, c k • δ k = ∑ k, c' k • δ' k → ∑ k, δ k = ∑ k, δ' k := by
  first | exact @GlobalTheory.TInj.coneSum_eq | exact GlobalTheory.TInj.coneSum_eq | (intros; apply GlobalTheory.TInj.coneSum_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeOfUniformisationEqModelLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeOfUniformisationEqModelLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat.UnifLat

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem exists_tau {o B X : Type} [CommRing o] [CommRing B] [AddCommGroup X] (b : o →+* B) (ζ : oˣ) {L : ℕ}
    (hL : 0 < L) (hζ : ζ ^ L = 1) (c : X →+ ZMod L) :
    ∃ τ : Multiplicative X →* Bˣ,
      (∀ χ, τ χ = Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ∧ τ ^ L = 1 := by
  haveI : NeZero L := ⟨hL.ne'⟩
  have hu : Units.map b.toMonoidHom ζ ^ L = 1 := by rw [← map_pow, hζ, map_one]
  refine ⟨{ toFun := fun χ => Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val
            map_one' := by simp
            map_mul' := fun χ χ' => by
              simp only [toAdd_mul, map_add (f := _), ZMod.val_add]
              rw [← pow_add, ← pow_eq_pow_mod _ hu] }, fun χ => rfl, ?_⟩
  refine MonoidHom.ext fun χ => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  show (Units.map b.toMonoidHom ζ ^ (c (Multiplicative.toAdd χ)).val) ^ L = 1
  rw [← pow_mul, mul_comm, pow_mul, hu, one_pow]

end GlobalTheory.Poinc.FibLat.UnifLat


open GlobalTheory.Poinc.FibLat.UnifLat in
theorem GlobalTheory.Poinc.FibLat.latAt_of_unif : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (Gu : Over (Sp V)) [GrpObj Gu] [IsCommMonObj Gu], IsSemiAbelian Gu → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A Gu) (F : I → (Gu ⟶ Gu)) (m : I → D.toPre.X →+ D.toPre.X), (∀ e, EndChar U (F e) (m e)) → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (fV : V →+* V'), IsLocalHom fV → ∀ (ξ : Sp V' ⟶ M.Z) (a : o →+* V'), ξ ≫ M.s = spMap a → ∀ (G' : Over (Sp V')) [GrpObj G'] (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left), IsGrpPullback G' Gu (spMap fV) β → IsGrpPullback G' G ξ β' → (∀ e, ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ (F e).left ∧ F'.left ≫ β' = β' ≫ (f e).left) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (iK : V' →+* K), Function.Injective iK → iK.comp fV = (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V)) → ∀ c : T → D.toPre.X →+ ZMod L, (∀ t, ExtNear (gγ t) (ξ (closedPoint V')) ∧ ∃ (q : QkPt D.toPre K L) (τ : Multiplicative D.toPre.X →* Kˣ) (x : TFK (R := V) K ⟶ A.A) (x' : Sp K ⟶ G'.left), q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkToAkU U.toUnifPre K L q x ∧ (∀ χ, (τ (Multiplicative.ofAdd χ) : K) = iK (a ((ζ : o) ^ (c t χ).val))) ∧ x' ≫ G'.hom = spMap iK ∧ x' ≫ β = x.left ≫ genMap U ∧ ValAt (gγ t) (spMap iK ≫ ξ) (x' ≫ β')) → LatAt f gγ ζ L m c (ξ (closedPoint V')) := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ V _ _ _ hV Gu _ _ hGu D A U F m hF V' _ _ _ fV hfV ξ a hξ G' _ β β'
    hβ hβ' hF' K _ _ _ iK hiK hKf c hc
  haveI : IsSeparated G.hom := hG.separated
  haveI : IsSeparated Gu.hom := hGu.separated
  haveI : IsSeparated G'.hom := MorphismProperty.of_isPullback (P := @IsSeparated) hβ.1 inferInstance
  obtain ⟨r, hrl, hr⟩ : ∃ r : V' →+* ResidueField V', IsLocalHom r ∧ ∀ x, r x = 0 ↔ x ∈ maximalIdeal V' :=
    ⟨residue V', inferInstance, fun x => residue_eq_zero_iff x⟩
  have hρ : ∀ x ∈ maximalIdeal V ^ (0 + 1), (r.comp fV) x = 0 := fun x hx => by
    rw [zero_add, pow_one] at hx
    exact (hr _).2 (map_nonunit fV x hx)
  obtain ⟨G₀, _, ψ, hψ⟩ : ∃ (G₀ : Over (Sp (ResidueField V'))) (_ : GrpObj G₀) (ψ : G₀.left ⟶ G'.left),
      IsGrpPullback G₀ G' (spMap r) ψ := ⟨_, inferInstance, _, isGrpPullback_pullback G' (spMap r)⟩
  have h₀ : IsGrpPullback G₀ Gu (spMap (r.comp fV)) (ψ ≫ β) := (hψ.comp hβ).congr (spMap_comp_eq fV r).symm rfl
  have hφ : IsGrpPullback G₀ G (spMap r ≫ ξ) (ψ ≫ β') := hψ.comp hβ'
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := GlobalTheory.ToricTorsionUnif.main V hV Gu hGu D A U L hL
  refine ⟨ResidueField V', inferInstance, spMap r ≫ ξ, r.comp a, G₀, inferInstance, ψ ≫ β',
    GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀, ?_, ?_, hφ, isTorPart_gtTorus _ hρ h₀, ?_⟩
  · show ξ ((spMap r) (closedPoint (ResidueField V'))) = _
    rw [spMap, Spec_closedPoint]
  · rw [Category.assoc, hξ, spMap_comp_eq a r]
  refine ⟨fun e => ?_, fun t => ?_⟩
  · obtain ⟨F', hF1, hF2⟩ := hF' e
    have w : (ψ ≫ F'.left) ≫ G'.hom = G₀.hom ≫ spMap r := by
      rw [Category.assoc, Over.w F', hψ.1.w]
    obtain ⟨F₀, hF₀⟩ : ∃ F₀ : G₀ ⟶ G₀, F₀.left ≫ ψ = ψ ≫ F'.left :=
      ⟨Over.homMk (hψ.1.lift (ψ ≫ F'.left) G₀.hom w) (hψ.1.lift_snd _ _ _), hψ.1.lift_fst _ _ _⟩
    have hE := hF e (ResidueField V') (r.comp fV) hρ G₀ (ψ ≫ β) h₀ F₀
      (by rw [← Category.assoc, hF₀, Category.assoc, hF1, Category.assoc])
    have k : (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left =
        (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V')) (m e) ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left := by
      rw [← Over.comp_left, hE]
    calc (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ (ψ ≫ β') ≫ (f e).left
        = (GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ ≫ F'.left ≫ β' := by rw [hF2]; simp only [Category.assoc]
      _ = ((GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ F₀.left) ≫ ψ ≫ β' := by
          rw [Category.assoc, reassoc_of% hF₀]
      _ = _ := by rw [k]
  · obtain ⟨hext, q, τ, x, x', hq, hτq, hqx, hτ, hx'1, hx'2, hx'3⟩ := hc t
    obtain ⟨τV, hτVv, hτV⟩ := exists_tau a ζ hL hζ (c t)
    obtain ⟨τκ, hτκv, hτκ⟩ := exists_tau (r.comp a) ζ hL hζ (c t)
    have hchar : ∀ χ, (τ χ : K) = iK (τV χ : V') := fun χ => by
      rw [hτVv]
      refine (hτ (Multiplicative.toAdd χ)).trans ?_
      simp
    have hcharκ : ∀ χ, (τκ χ : ResidueField V') = r (τV χ : V') := fun χ => by
      rw [hτVv, hτκv]
      simp
    have hτL : τ ^ L = 1 := MonoidHom.ext fun χ => Units.ext (by
      rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hchar, ← map_pow, ← Units.val_pow_eq_pow_val,
        ← MonoidHom.pow_apply, hτV]
      simp)
    have hσ₀ : (s V' fV τV hτV).left ≫ Gu.hom = 𝟙 (Sp V') ≫ spMap fV :=
      (Over.w (s V' fV τV hτV)).trans (Category.id_comp _).symm
    obtain ⟨σ, hσβ, hσG⟩ : ∃ σ : Sp V' ⟶ G'.left, σ ≫ β = (s V' fV τV hτV).left ∧ σ ≫ G'.hom = 𝟙 _ :=
      ⟨hβ.1.lift _ _ hσ₀, hβ.1.lift_fst _ _ _, hβ.1.lift_snd _ _ _⟩
    obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ hext
    obtain ⟨σ', hσ'β, hσ'G⟩ : ∃ σ' : Sp V' ⟶ G'.left, σ' ≫ β' = v ∧ σ' ≫ G'.hom = 𝟙 _ :=
      ⟨hβ'.1.lift v (𝟙 _) (by rw [hv.over, Category.id_comp]), hβ'.1.lift_fst _ _ _, hβ'.1.lift_snd _ _ _⟩
    have eσK : spMap iK ≫ σ = x' := hβ.1.hom_ext (by
        rw [Category.assoc, hσβ, hx'2, hs4 K (iK.comp fV) τ hτL q x hKf hq hτq hqx,
          hs2 V' K fV (iK.comp fV) iK τV hτV τ hτL rfl hchar])
      (by rw [Category.assoc, hσG, hx'1, Category.comp_id])
    have eσ'K : spMap iK ≫ σ' = x' := hβ'.1.hom_ext (by
        rw [Category.assoc, hσ'β]; exact ValAt.unique (hv.comp (spMap iK)) hx'3)
      (by rw [Category.assoc, hσ'G, hx'1, Category.comp_id])
    haveI : IsDominant (spMap iK) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical iK).2
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hiK]; exact bot_le)⟩
    have eσ : σ = σ' := ext_of_isDominant_of_isSeparated G'.hom (by rw [hσG, hσ'G]) (spMap iK)
      (eσK.trans eσ'K.symm)
    let φκ : Multiplicative D.toPre.X →* Γ((Over.mk (𝟙 (Sp (ResidueField V')))).left, ⊤)ˣ :=
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of (ResidueField V'))).inv.hom.toMonoidHom).comp τκ
    obtain ⟨z, hz⟩ : ∃ z : Over.mk (𝟙 (Sp (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X,
        ∀ χ, GlobalTheory.UU.chV z χ = unitOn (τκ (Multiplicative.ofAdd χ)) :=
      ⟨(GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ, fun χ => by
        show GlobalTheory.splitTorusPointsEquiv _ _ _ ((GlobalTheory.splitTorusPointsEquiv _ _ _).symm φκ) _ = _
        rw [MulEquiv.apply_symm_apply]; rfl⟩
    have hz1w : z.left ≫ (splitTorus (Sp (ResidueField V')) D.toPre.X).hom =
        (Over.mk (spMap (RingHom.id (ResidueField V')))).hom := by
      rw [Over.w z]
      show 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id (ResidueField V')))
      rw [CommRingCat.ofHom_id, Spec.map_id]
    let z₁ : Over.mk (spMap (RingHom.id (ResidueField V'))) ⟶ splitTorus (Sp (ResidueField V')) D.toPre.X :=
      Over.homMk z.left hz1w
    have hz₁ : ∀ χ, GlobalTheory.UU.chV z₁ χ = unitOn (τκ (Multiplicative.ofAdd χ)) := fun χ =>
      (Units.ext (by rw [GlobalTheory.UU.chV_val, GlobalTheory.UU.chV_val]; rfl)).trans (hz χ)
    have e3 := hs3 (ResidueField V') (ResidueField V') (r.comp fV) hρ (r.comp fV) (RingHom.id _) G₀ (ψ ≫ β) h₀ τκ hτκ
      z₁ (RingHom.id_comp _).symm hz₁
    have e2 := hs2 V' (ResidueField V') fV (r.comp fV) r τV hτV τκ hτκ rfl hcharκ
    have ez : (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hρ h₀).left ≫ ψ = spMap r ≫ σ := hβ.1.hom_ext
      (by
        rw [Category.assoc, Category.assoc, hσβ, ← e2, e3]
        rfl)
      (by
        rw [Category.assoc, Category.assoc, hσG, Category.comp_id, hψ.1.w, ← Category.assoc,
          Over.w (z ≫ _)]
        exact Category.id_comp _)
    refine ⟨z, fun χ => (hz χ).trans (by rw [hτκv]; rfl), ?_⟩
    rw [← Category.assoc, ez, eσ, Category.assoc, hσ'β]
    exact hv.comp (spMap r)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeOfUniformisationEqModelLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_of_uniformisation_eq_model_lattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (Gu : Over (Sp V)) [GrpObj Gu] [IsCommMonObj Gu], IsSemiAbelian Gu → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A Gu) (F : I → (Gu ⟶ Gu)) (m : I → D.toPre.X →+ D.toPre.X), (∀ e, EndChar U (F e) (m e)) → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (fV : V →+* V'), IsLocalHom fV → ∀ (ξ : Sp V' ⟶ M.Z) (a : o →+* V'), ξ ≫ M.s = spMap a → ∀ (G' : Over (Sp V')) [GrpObj G'] (β : G'.left ⟶ Gu.left) (β' : G'.left ⟶ G.left), IsGrpPullback G' Gu (spMap fV) β → IsGrpPullback G' G ξ β' → (∀ e, ∃ F' : G' ⟶ G', F'.left ≫ β = β ≫ (F e).left ∧ F'.left ≫ β' = β' ≫ (f e).left) → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (iK : V' →+* K), Function.Injective iK → iK.comp fV = (algebraMap (FractionRing V) K).comp (algebraMap V (FractionRing V)) → ∀ c : T → D.toPre.X →+ ZMod L, (∀ t, ExtNear (gγ t) (ξ (closedPoint V')) ∧ ∃ (q : QkPt D.toPre K L) (τ : Multiplicative D.toPre.X →* Kˣ) (x : TFK (R := V) K ⟶ A.A) (x' : Sp K ⟶ G'.left), q.y = 0 ∧ GlobalTheory.UT.IsTor τ q.g ∧ QkToAkU U.toUnifPre K L q x ∧ (∀ χ, (τ (Multiplicative.ofAdd χ) : K) = iK (a ((ζ : o) ^ (c t χ).val))) ∧ x' ≫ G'.hom = spMap iK ∧ x' ≫ β = x.left ≫ genMap U ∧ ValAt (gγ t) (spMap iK ≫ ξ) (x' ≫ β')) → LatAt f gγ ζ L m c (ξ (closedPoint V')) := by
  first | exact @GlobalTheory.Poinc.FibLat.latAt_of_unif | exact GlobalTheory.Poinc.FibLat.latAt_of_unif | (intros; apply GlobalTheory.Poinc.FibLat.latAt_of_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemThetaConstantNegEvenUpToRoot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemThetaConstantNegEvenUpToRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.ThetaParity

theorem exists_rigPull_inv {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (hrig : rig.IsGen) :
    haveI := P.isAb.comm
    ∃ w : LB.Iso P.L (P.L.pull (ι[P.A]).left), GlobalTheory.OneBasis.RigPull P.A P.A (𝟙 S) (ι[P.A]).left w rig rig := by
  haveI := P.isAb.comm
  obtain ⟨u, hu⟩ := GlobalTheory.exists_gen_neg_of_sym GlobalTheory.globalFns_holds P.isAb P.isLB P.sym
  obtain ⟨s, hs, hr⟩ := GlobalTheory.AbPackage.exists_rigidified_sym P.isLB u hu
  let L : RigLB P.A := ⟨P.L, rig, P.isLB, hrig⟩
  obtain ⟨he, w, hw, hm⟩ := GlobalTheory.SymmetricBundle.isSymmetric_of_gen L s hs hr
  refine ⟨w, GlobalTheory.SabBaseChange.isGrpPullback_inv P.A, hw, hrig, ?_⟩
  exact (maps_iff w (K := PUnit) (fun _ => eSec P.A) (fun _ => eSec P.A) (fun _ => 1) rig rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) he P.L j) (fun _ => rfl)).1 hm

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem pt_neg {S : ThetaSys o Ω} (ρ : S.Real) (a : S.Gam) : ρ.pt (-a) = (ρ.pt a)⁻¹ := by
  have h0 : ρ.pt 0 = 1 := by
    have h := ρ.pt_add 0 0
    rw [add_zero] at h
    have h' : ρ.pt 0 * ρ.pt 0 = ρ.pt 0 * 1 := by rw [_root_.mul_one]; exact h.symm
    exact mul_left_cancel h'
  have h := ρ.pt_add (-a) a
  rw [neg_add_cancel, h0] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem pt_neg_left {S : ThetaSys o Ω} (ρ : S.Real) (a : S.Gam) :
    haveI := ρ.P.isAb.comm
    (ρ.pt (-a)).left ≫ (ι[ρ.P.A]).left = 𝟙 _ ≫ (ρ.pt a).left := by
  rw [pt_neg, Category.id_comp, ← Over.comp_left]
  congr 1
  simp [Hom.inv_def]

theorem key_fn (S : ThetaSys o Ω) (ρ : S.Real) :
    ∃ c₀ : Γ((baseOver (Sp S.R)).left, ⊤), ∀ a, ∃ d : Γ((baseOver (Sp S.R)).left, ⊤),
      d ^ ((S.r * S.N) ^ 2) = 1 ∧ c₀ * fn (⟨S.th (-a), S.th_mem (-a)⟩ : S.R) = d * fn (⟨S.th a, S.th_mem a⟩ : S.R) := by
  haveI := ρ.P.isAb.comm
  obtain ⟨w, R⟩ := exists_rigPull_inv ρ.P ρ.rig ρ.rig_gen
  have hφ : (ι[ρ.P.A]).left ≫ ρ.P.A.hom = ρ.P.A.hom ≫ 𝟙 _ := by rw [Over.w, Category.comp_id]
  obtain ⟨s', hs', -⟩ := GlobalTheory.OneBasis.Calc.existsUnique_thru (k := 1) (T := baseOver (Sp S.R))
    (T' := baseOver (Sp S.R)) hφ R.2.1 ρ.P.isLB ρ.P.isLB (h := 𝟙 _) (by simp) ρ.th₁
  obtain ⟨c, hc, -⟩ := ρ.th₁_basis s'
  refine ⟨c 0, fun a => ?_⟩
  obtain ⟨e', he', He⟩ := GlobalTheory.OneBasis.TabMap.frame_move R (h := 𝟙 _) (pt_neg_left ρ a) (ρ.fr_tors a)
  have v₁ := He 1 ρ.th₁ s' (fn (⟨S.th a, S.th_mem a⟩ : S.R)) hs' (fun z J hJ => by
    have := GlobalTheory.FrameMove.sval_valueAt (ρ.th_val a) (𝟙 _) hJ
    rw [Category.id_comp] at this
    rw [GlobalTheory.FrameMove.val_powFrame]
    simpa using this)
  have v₂ := (GlobalTheory.OneBasis.Calc.cmb_iff ρ.P.isLB (k := 1) (fun _ => ρ.th₁) c s').1 hc
  obtain ⟨d, hd⟩ := GlobalTheory.AbPackage.exists_unit_ratio ρ.P.isLB he'.2.1 (ρ.fr_tors (-a)).2.1
  obtain ⟨α, hα⟩ := GlobalTheory.EmbLocal.exists_mulPull GlobalTheory.globalFns_holds ρ.P (S.r * S.N) (baseOver (Sp S.R))

  refine ⟨(d : Γ((baseOver (Sp S.R)).left, ⊤)), ?_, ?_⟩
  · have hu : d ^ ((S.r * S.N) ^ 2) = 1 := by
      apply Units.ext
      apply fn_ext
      intro z _
      obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' ρ.P.isLB z
      have t₁ := GlobalTheory.ThetaCompare.torsFrame_pow GlobalTheory.globalFns_holds ρ.P hα he' hJ
      have t₂ := GlobalTheory.ThetaCompare.torsFrame_pow GlobalTheory.globalFns_holds ρ.P hα (ρ.fr_tors (-a)) hJ
      have e := hd _ (𝟙 _) z J hJ
      rw [e, mul_pow, ← t₂, _root_.mul_assoc] at t₁
      have g := mul_eq_right.1 t₁
      rw [gs_unit (𝟙 _) z ⊤ trivial, gs_unit (𝟙 _) z ⊤ trivial, map_pow, g, map_one]
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  · apply fn_ext
    intro z _
    obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' ρ.P.isLB z
    have a₁ := v₁ z J hJ
    have a₂ := v₂ _ (ptSecT ρ.P.A (ρ.pt (-a))).left z J hJ
    have a₃ := GlobalTheory.FrameMove.sval_valueAt (ρ.th_val (-a)) (𝟙 _) hJ
    have a₄ := hd _ (𝟙 _) z J hJ
    rw [Category.id_comp] at a₃
    rw [gs_mul _ z ⊤ trivial, gs_mul _ z ⊤ trivial]

    simp only [GlobalTheory.FrameGen.sv, Fin.sum_univ_one] at a₂
    have f₁ : (ptSecT ρ.P.A (ρ.pt (-a))).left ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left = 𝟙 _ := by
      rw [← Over.comp_left, ptSecT, lift_fst, Over.id_left]
    rw [f₁, ← GlobalTheory.FrameGen.gs_top, a₃] at a₂
    have hp : ∀ u : ((baseOver (Sp S.R)).left.presheaf.stalk z)ˣ, u ^ ((1 : ℕ) : ℤ) = u := fun u => by simp
    rw [GlobalTheory.FrameMove.val_powFrame, hp, a₄, Units.val_mul] at a₁
    have e := a₂.symm.trans a₁
    rw [← gs_unit (𝟙 _) z ⊤ trivial d] at e
    refine (Units.mul_left_inj (Geo.Tor.val (ρ.fr (-a)) (𝟙 _) z J)).1 ?_
    linear_combination e

theorem key (S : ThetaSys o Ω) (ρ : S.Real) :
    ∃ C : Ω, ∀ a, ∃ D : Ω, D ^ ((S.r * S.N) ^ 2) = 1 ∧ C * S.th (-a) = D * S.th a := by
  obtain ⟨c₀, h⟩ := key_fn S ρ
  let φ : Γ((baseOver (Sp S.R)).left, ⊤) →+* Ω :=
    S.R.val.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of S.R)).hom.hom
  have hφ : ∀ x : S.R, φ (fn x) = x := fun x => by simp [φ, fn]
  refine ⟨φ c₀, fun a => ?_⟩
  obtain ⟨d, hd, e⟩ := h a
  refine ⟨φ d, by rw [← map_pow, hd, map_one], ?_⟩
  have := congrArg φ e
  rwa [map_mul, map_mul, hφ, hφ] at this

theorem odd_rN (S : ThetaSys o Ω) (ρ : S.Real) : Odd ((S.r * S.N) ^ 2) := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  rw [hj, ρ.N_eq]
  exact ((ρ.n_odd.pow).mul ((ρ.n_odd.pow).pow)).pow

end GlobalTheory.ThetaParity

namespace GlobalTheory.ThetaParity

theorem theta_neg : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (ρ : S.Real) (a : S.Gam), ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a := by
  intro o Ω _ _ _ _ S ρ a
  obtain ⟨C, hC⟩ := key S ρ
  have hodd := odd_rN S ρ
  set m := (S.r * S.N) ^ 2 with hm
  obtain ⟨x, hx⟩ := S.th_ne
  obtain ⟨D₁, hD₁, e₁⟩ := hC x
  obtain ⟨D₂, hD₂, e₂⟩ := hC (-x)
  rw [neg_neg] at e₂
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have nz : ∀ D : Ω, D ^ m = 1 → D ≠ 0 := fun D h h0 => by
    rw [h0, zero_pow hm0] at h; exact zero_ne_one h
  have hx' : S.th (-x) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at e₁; exact (mul_ne_zero (nz _ hD₁) hx) e₁.symm
  have hC0 : C ≠ 0 := by
    intro h0; rw [h0, zero_mul] at e₁; exact (mul_ne_zero (nz _ hD₁) hx) e₁.symm
  have hC2 : C ^ 2 = D₁ * D₂ := by
    have h2 : C ^ 2 * (S.th (-x) * S.th x) = D₁ * D₂ * (S.th (-x) * S.th x) := by
      linear_combination (C * S.th x) * e₁ + (D₁ * S.th x) * e₂
    exact mul_right_cancel₀ (mul_ne_zero hx' hx) h2
  have hCi : C⁻¹ ^ (2 * m) = 1 := by
    rw [inv_pow, pow_mul, hC2, mul_pow, hD₁, hD₂, _root_.one_mul, inv_one]
  obtain ⟨D, hD, e⟩ := hC a
  obtain ⟨k, hk⟩ := hodd
  refine ⟨C⁻¹ ^ m, C⁻¹ ^ (m + 1) * D, ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, hCi]
  · rw [mul_pow, hD, _root_.mul_one, ← pow_mul, show (m + 1) * m = 2 * m * (k + 1) by rw [hk]; ring, pow_mul, hCi,
      one_pow]
  · have e' : S.th (-a) = C⁻¹ * D * S.th a := by
      rw [_root_.mul_assoc, ← e, ← _root_.mul_assoc, inv_mul_cancel₀ hC0, _root_.one_mul]
    rw [e', ← _root_.mul_assoc, ← pow_add, show m + (m + 1) = 2 * m + 1 by ring, pow_succ, hCi, _root_.one_mul]

end GlobalTheory.ThetaParity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedThetaSystemThetaConstantNegEvenUpToRootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisedThetaSystem_thetaConstant_neg_even_upToRoot : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (a : S.Gam), ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a := by
  first | exact @GlobalTheory.ThetaParity.theta_neg | exact GlobalTheory.ThetaParity.theta_neg | (intros; apply GlobalTheory.ThetaParity.theta_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyUnitPowTwistingSectionOnComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyUnitPowTwistingSectionOnComponent
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
open IsDedekindDomain GlobalTheory.LamT GlobalTheory.KeyFourth
open GlobalTheory.AllWt

namespace GlobalTheory.KeyPowTw

theorem exists_twSec_key (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (K : (Rul Xo c)ˣ) (C : (c.F →+* ℂ) → ℝ) (hP : HasPts U Z) (hks : Nonempty (KeySec Xo c)) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hpq : 1 ≤ Dw.p + Dw.q) (hKmem : (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw)) (hCpos : ∀ σ, 0 < C σ) (hCeq : ∀ σ, ∀ k, ∀ y ∈ ((U (goodOf c σ)).X k).dom, homN (U (goodOf c σ)) x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C σ) (hval : ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (K : Rul Xo c) ∧ v (K : Rul Xo c) ≤ ((4 * ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ) : ℝ) : EReal)) :
    ∃ t : TwSec U x Z (wtOf Dw 0 (-4)), (∀ w, t.lo w = 0) ∧ ∀ σ, t.cInf σ = C σ := by
  have hwt : ∀ (m : ℤ) (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → (wtOf Dw 0 m).1 (τ, i) = -m :=
    GlobalTheory.KeyRootTw.wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 (-4)) = (4 : ℤ) • keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · show (2 * (-4) : ℤ) = 4 * (-2)
      norm_num
    · show (wtOf Dw 0 (-4)).1 (τ, (i : ℕ)) = 4 * 1
      rw [hwt (-4) τ i i.2]; norm_num
  have hadd : wtOf Dw 0 (-4) + wtOf Dw 0 4 = 0 := by
    rw [← wtOf_add, add_zero, neg_add_cancel, wtOf_zero]
  have hneg : -wtOf Dw 0 (-4) = wtOf Dw 0 4 := neg_eq_of_add_eq_zero_right hadd
  have hi := idem_mul_idem Z
  set s : Rul Xo c := idem Z * (K : Rul Xo c) with hs
  set s' : Rul Xo c := idem Z * ((K⁻¹ : (Rul Xo c)ˣ) : Rul Xo c) with hs'
  have hsm : s ∈ secZ Xo c (exZ Dw (wtOf Dw 0 (-4))) := by
    have := mul_mem_secZ (idem_mem_secZ Z) hKmem
    rwa [zero_add, ← hex] at this
  have hsm' : s' ∈ secZ Xo c (exZ Dw (wtOf Dw 0 4)) := by
    have := mul_mem_secZ (idem_mem_secZ Z) (inv_mem_secZ hKmem)
    rwa [zero_add, ← hex, ← exZ_neg_eq, hneg] at this
  have hsupp : s ∈ suppOn Z := by rw [hs, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hsupp' : s' ∈ suppOn Z := by rw [hs', mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  have hss' : s * s' = idem Z := by rw [hs, hs', mul_mul_mul_comm, hi, Units.mul_inv, mul_one]
  have hnorm : ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z,
      homN (U (goodOf c σ)) x (wtOf Dw 0 (-4)) s z = C σ ∧ homN (U (goodOf c σ)) x (wtOf Dw 0 4) s' z = (C σ)⁻¹ := by
    intro σ z hz
    obtain ⟨hd, hl⟩ := hz
    have h1 := homN_idem (U (goodOf c σ)) x hd hl ((hP.1 σ).2 z ⟨hd, hl⟩ hd)
    have hm : ∀ (m m' : ℤ) (f g : Rul Xo c), homN (U (goodOf c σ)) x (wtOf Dw 0 (m + m')) (f * g) z =
        homN (U (goodOf c σ)) x (wtOf Dw 0 m) f z * homN (U (goodOf c σ)) x (wtOf Dw 0 m') g z := fun m m' f g => by
      rw [← homN_mul _ x (even_wtOf _ _) (even_wtOf _ _) f g z hd, ← wtOf_add, add_zero]
    rw [← wtOf_zero (Dw := Dw)] at h1
    have h2 : homN (U (goodOf c σ)) x (wtOf Dw 0 (-4)) s z = C σ := by
      have := hm 0 (-4) (idem Z) K
      rw [zero_add, h1, one_mul] at this
      rw [hs, this, hCeq σ z.1 z.2 hd]
    refine ⟨h2, ?_⟩
    have h5 := hm (-4) 4 s s'
    rw [hss', neg_add_cancel, h1, h2] at h5
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h5.symm)
  have hgood : ∀ σ, GoodEmb c σ → goodOf c σ = σ := fun σ h => if_pos h
  have hmono : ∀ (m : ℤ) (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ →
      (wtOf Dw 0 m).1 (τ, j) ≤ (wtOf Dw 0 m).1 (τ, i) := fun m τ i j hij hj => by
    rw [hwt m τ i (lt_of_le_of_lt hij hj), hwt m τ j hj]
  have hbd : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 (-4)) s z ≤ D := by
    intro σ hσ
    refine ⟨C σ, fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).1.le
  have hbd' : ∀ σ, GoodEmb c σ → ∃ D : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw 0 4) s' z ≤ D := by
    intro σ hσ
    refine ⟨(C σ)⁻¹, fun z hz => ?_⟩
    have h1 := hnorm σ
    rw [hgood σ hσ] at h1
    exact (h1 z hz).2.le
  let B : HeightOneSpectrum (𝓞 c.F) → ℝ := fun w =>
    ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (ord_vw w (conjDifferent (embF c τ)) : ℝ)
  have hvs : ∀ w, ∀ v ∈ valOn Z w, v s = v (K : Rul Xo c) := fun w v hv => by
    rw [hs, (isVal_valOn hv).mul, val_idem hv, zero_add]
  let t : TwSec U x Z (wtOf Dw 0 (-4)) :=
    { even := even_wtOf _ _
      sig := s
      inv := s'
      sig_mem := hsm
      inv_mem := by rw [← exZ_neg_eq, hneg]; exact hsm'
      idem_sig := by rw [hs, ← mul_assoc, hi]
      idem_inv := by rw [hs', ← mul_assoc, hi]
      mul_inv := hss'
      cInf := C
      cInf_pos := hCpos
      norm_inf := fun σ z hz => (hnorm σ z hz).1
      cusp_sig := fun G hG f hf =>
        GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 (-4)) s hks hU hpq (even_wtOf _ _) (hmono (-4)) hsm hsupp hbd G hG f hf
      cusp_inv := fun G hG f hf => by
        have h7 := GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component E H Dw l Xo c r U x Z (wtOf Dw 0 4) s' hks hU hpq (even_wtOf _ _) (hmono 4)
          hsm' hsupp' hbd' (G + wtOf Dw 0 (-4)) (hG.add (even_wtOf _ _)) f hf
        rwa [add_assoc, hadd, add_zero] at h7
      lo := fun _ => 0
      hi := fun w => 4 * B w
      lo_le := fun w v hv => by
        rw [hvs w v hv]; exact_mod_cast (hval w v (valOn_subset Z w hv)).1
      le_hi := fun w v hv => by
        rw [hvs w v hv]; exact (hval w v (valOn_subset Z w hv)).2
      finite_lo := by simp
      finite_hi := by
        refine (Set.finite_iUnion fun τ => finite_ord (embF c τ)).subset fun w hw => ?_
        by_contra hn
        simp only [Function.mem_support, Set.mem_iUnion, not_exists, not_not] at hn
        apply hw
        simp [B, hn]
      pts := hP }
  exact ⟨t, fun _ => rfl, fun _ => rfl⟩

theorem exists_twSec_keyPow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ (Z : Comp Xo c) (m : ℕ), ∃ t : GlobalTheory.FlatTw.TwSec U x Z (wtOf Dw 0 (-(4 * (m : ℤ)))), (∀ w, 0 ≤ t.lo w) ∧ ∀ σ, Real.log (t.cInf σ) ≤ (m : ℝ) * (2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi)) := by
  intro E _ _ _ H Dw l Xo c r U x hU hx hF hpq hg
  obtain ⟨κ, k₁, k₂, k₃, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hpq
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨ρ, -⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hU _ hσ0) hF hpq hKmem hKval
  have hkr : GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ := by
    refine ⟨?_, k₂, k₃, k₄, ?_⟩
    · simpa only [GlobalTheory.KeyCl.Homog, mul_one] using k₁
    · simpa only [GlobalTheory.KeyCl.ArchNorm, mul_one] using k₅
  have hval := GlobalTheory.T.theta_key_section_valuation_bounds_different κ hkr E H Dw l Xo c _ e K hpq hg hKmem hKval
  have hC := fun σ : c.F →+* ℂ => GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow κ k₁ k₂ k₅ E H Dw l Xo c _ e (goodOf c σ) r (U (goodOf c σ)) x K
    (goodEmb_goodOf c σ) (hU _ (goodEmb_goodOf c σ)) (hx _ (goodEmb_goodOf c σ)) ⟨ρ⟩ hpq hKmem hKval
  choose C hCpos hClog hCeq using hC
  have hgE := card_frame_index Dw e
  have hpsi : Nat.card (Psi H) = Module.finrank ℚ E / 2 := GlobalTheory.PeriodCoord.card_cmType H
  have hCb : ∀ σ, Real.log (C σ) ≤ 2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi) :=
    fun σ => by rw [hpsi, hgE]; exact (abs_le.1 (hClog σ)).2
  refine ⟨⟨ρ⟩, fun Z m => ?_⟩
  have hP : HasPts U Z := hasPts U hpq hg hU Z
  obtain ⟨t₁, ht₁lo, ht₁c⟩ := exists_twSec_key E H Dw l Xo c r U x Z K C hP ⟨ρ⟩ hU hpq hKmem hCpos hCeq hval
  induction m with
  | zero =>
    have h0 : (0 : WTZ E) = wtOf Dw 0 (-(4 * ((0 : ℕ) : ℤ))) := by simp [wtOf_zero]
    obtain ⟨-, h2, h3, -, -⟩ := TwSec.const_spec (x := x) hP 1 one_ne_zero
    refine ⟨(TwSec.const x hP 1 one_ne_zero).copy h0, fun w => ?_, fun σ => ?_⟩
    · show 0 ≤ (TwSec.const x hP 1 one_ne_zero).lo w
      rw [h3]; simp [vAdd]
    · show Real.log ((TwSec.const x hP 1 one_ne_zero).cInf σ) ≤ _
      rw [h2]; simp
  | succ m ih =>
    obtain ⟨t, htlo, htc⟩ := ih
    have h0 : wtOf Dw 0 (-(4 * (m : ℤ))) + wtOf Dw 0 (-4) = wtOf Dw 0 (-(4 * ((m + 1 : ℕ) : ℤ))) := by
      rw [← wtOf_add, add_zero]; congr 1; push_cast; ring
    refine ⟨(t.mul t₁).copy h0, fun w => ?_, fun σ => ?_⟩
    · show 0 ≤ t.lo w + t₁.lo w
      rw [ht₁lo]; linarith [htlo w]
    · show Real.log (t.cInf σ * t₁.cInf σ) ≤ _
      rw [Real.log_mul (t.cInf_pos σ).ne' (t₁.cInf_pos σ).ne', ht₁c]
      have h1 := htc σ
      have h2 := hCb σ
      push_cast at h1 h2 ⊢
      linarith

end GlobalTheory.KeyPowTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyUnitPowTwistingSectionOnComponentStatement
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyUnit_pow_twistingSection_on_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → Nonempty (GlobalTheory.ShFam.KeySec Xo c) ∧ ∀ (Z : Comp Xo c) (m : ℕ), ∃ t : GlobalTheory.FlatTw.TwSec U x Z (wtOf Dw 0 (-(4 * (m : ℤ)))), (∀ w, 0 ≤ t.lo w) ∧ ∀ σ, Real.log (t.cInf σ) ≤ (m : ℝ) * (2 * ((Nat.card (Psi H) * (Dw.p + Dw.q) : ℕ) : ℝ) * Real.log (2 * Real.pi)) := by
  first | exact @GlobalTheory.KeyPowTw.exists_twSec_keyPow | exact GlobalTheory.KeyPowTw.exists_twSec_keyPow | (intros; apply GlobalTheory.KeyPowTw.exists_twSec_keyPow <;> assumption)
end
end
