module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutFormFixedByIntegralPointsAlmostAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutFormFixedByIntegralPointsAlmostAllPlaces
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AutFormFix

open Matrix GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem eq_one_of_forall_cLoc {x : UA E a} (hx : x ∈ finU (E := E) (n := a)) (h : ∀ u, cLoc u x = 1) : x = 1 := by
  refine Subtype.ext (ga_ext ?_ ?_)
  · exact (MonoidHom.mem_ker.1 hx).trans (map_one _).symm
  · rw [Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij] <;> rfl

theorem mem_integral_iff (k : finU (E := E) (n := a)) :
    k ∈ (AdelicGLn.integralFiniteGL E a).comap (finPart E a) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rw [Subgroup.mem_comap, AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem isCompact_integral :
    IsCompact (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a))) := by
  have hO : IsOpen (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a))) :=
    (AdelicGLn.isOpen_integralFiniteGL E a).preimage continuous_finPart
  refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
    ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad))
    (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E a x, hx, ?_⟩
  have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

end GlobalTheory.Cong.AutFormFix

namespace GlobalTheory.Cong.AutFormFix

open Matrix GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

theorem fixed_intU_eventually : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ : UA E a → ℂ),
    IsAutFormU φ → ∀ᶠ w in Filter.cofinite, ∀ x ∈ GlobalTheory.Cong.AdaptLev.intU a w, RU E a x φ = φ := by
  intro E _ _ _ a φ hφ
  classical
  set St : Set (finU (E := E) (n := a)) := {k : finU (E := E) (n := a) | RU E a k φ = φ} with hSt
  set K₀ : Set (finU (E := E) (n := a)) := (((AdelicGLn.integralFiniteGL E a).comap (finPart E a) : Subgroup (finU (E := E) (n := a))) : Set (finU (E := E) (n := a)))
  let t : Finset (HeightOneSpectrum (𝓞 E)) → Set (finU (E := E) (n := a)) := fun S =>
    {k : finU (E := E) (n := a) | ∀ u ∈ S, cLoc u k.1 = 1} ∩ Stᶜ
  have htc : ∀ S, IsClosed (t S) := by
    intro S
    refine IsClosed.inter ?_ hφ.level.isClosed_compl
    have : {k : finU (E := E) (n := a) | ∀ u ∈ S, cLoc u k.1 = 1} = ⋂ u ∈ S, {k : finU (E := E) (n := a) | cLoc u k.1 = 1} := by
      ext k; simp
    rw [this]
    refine isClosed_biInter fun u _ => ?_
    haveI : T2Space (GL (Fin a) (u.adicCompletion E)) := Units.isEmbedding_embedProduct.t2Space
    exact isClosed_eq ((continuous_cLoc u).comp continuous_subtype_val) continuous_const
  have hst : K₀ ∩ ⋂ S, t S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun k hk => ?_
    have hall : ∀ u, cLoc u k.1 = 1 := fun u =>
      (Set.mem_iInter.1 hk.2 {u}).1 u (Finset.mem_singleton_self u)
    have h1 : k = 1 := Subtype.ext (eq_one_of_forall_cLoc k.2 hall)
    have hnot := (Set.mem_iInter.1 hk.2 ∅).2
    apply hnot
    rw [h1]
    show RU E a ((1 : finU (E := E) (n := a)) : UA E a) φ = φ
    rw [Subgroup.coe_one, map_one]; rfl
  have hdt : Directed (· ⊇ ·) t := by
    intro S₁ S₂
    refine ⟨S₁ ∪ S₂, ?_, ?_⟩ <;> rintro k ⟨hk, hk'⟩ <;> refine ⟨fun u hu => hk u ?_, hk'⟩ <;> simp [hu]
  obtain ⟨S, hS⟩ := isCompact_integral.elim_directed_family_closed t htc (Set.disjoint_iff_inter_eq_empty.mpr hst) hdt
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ u ∈ S, Apart u w}.Finite := by
    refine ((S.finite_toSet.biUnion fun u _ => (Set.toFinite ({u, conjSrc (GlobalTheory.SplitPts.conjE E) u} : Set _)))).subset ?_
    intro w hw
    simp only [Set.mem_setOf_eq, not_forall, Apart, not_not] at hw
    obtain ⟨u, hu, he⟩ := hw
    refine Set.mem_biUnion hu ?_
    rcases eq_or_eq_conjSrc he.symm with rfl | rfl
    · simp
    · simp
  refine Filter.eventually_cofinite.2 (hfin.subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  intro hS'
  apply hw
  intro x hx
  obtain ⟨hxl, hxi⟩ := GlobalTheory.Cong.AdaptLev.mem_intU.1 hx
  have hxf : x ∈ finU (E := E) (n := a) := (Subgroup.mem_inf.1 hxl).1
  have hcomp : ∀ u, Apart u w → cLoc u x = 1 := fun u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hxl).2 u) hu)
  have hK : (⟨x, hxf⟩ : finU (E := E) (n := a)) ∈ K₀ := by
    refine (mem_integral_iff _).2 fun u => ?_
    by_cases hu : Apart u w
    · show cLoc u x ∈ _
      rw [hcomp u hu]; exact one_mem _
    · exact hxi u hu
  by_contra hne
  have : (⟨x, hxf⟩ : finU (E := E) (n := a)) ∈ K₀ ∩ t S := ⟨hK, fun u hu => hcomp u (hS' u hu), hne⟩
  exact (Set.disjoint_left.mp hS) this.1 this.2

end GlobalTheory.Cong.AutFormFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutFormFixedByIntegralPointsAlmostAllPlacesStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autForm_fixed_by_integralPoints_almostAllPlaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ : UA E a → ℂ), IsAutFormU φ → ∀ᶠ w in Filter.cofinite, ∀ x ∈ GlobalTheory.Cong.AdaptLev.intU a w, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.AutFormFix.fixed_intU_eventually) | (exact GlobalTheory.Cong.AutFormFix.fixed_intU_eventually) | (intros; apply GlobalTheory.Cong.AutFormFix.fixed_intU_eventually  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedOfFixedByLocalLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedOfFixedByLocalLevels
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AdaptLevFix

open GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem eq_one_of_forall_cLoc {x : UA E a} (hx : x ∈ finU (E := E) (n := a)) (h : ∀ u, cLoc u x = 1) : x = 1 := by
  have hinf : cInf x = 1 := MonoidHom.mem_ker.1 hx
  refine Subtype.ext (ga_ext ?_ ?_)
  · exact hinf.trans (map_one _).symm
  · rw [Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin a) (u.adicCompletion E) => g.val i j) (h u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij] <;> rfl

theorem isCompact_integral :
    IsCompact {k : finU (E := E) (n := a) | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a)} := by
  have e' : ∀ k : finU (E := E) (n := a), k ∈ (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap
      (GlobalTheory.BCT.GlobLev.finPart E a) ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
    intro k
    rw [Subgroup.mem_comap, GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
    simp only [GlobalTheory.BCT.GlobLev.mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
    exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
      fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩
  have e : {k : finU (E := E) (n := a) | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a)} =
      ((GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap (GlobalTheory.BCT.GlobLev.finPart E a) :
        Set (finU (E := E) (n := a))) := by
    ext k
    exact (e' k).symm
  have hO : IsOpen ((GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a).comap (GlobalTheory.BCT.GlobLev.finPart E a) :
      Set (finU (E := E) (n := a))) :=
    (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a).preimage GlobalTheory.BCT.GlobLev.continuous_finPart
  rw [e]
  refine IsCompact.of_isClosed_subset (GlobalTheory.BCT.GlobLev.isClosedEmbedding_finU.isCompact_preimage
      ((GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E a).image GlobalTheory.BCT.GlobLev.continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨GlobalTheory.BCT.GlobLev.finPart E a x, hx, ?_⟩
  have h1 : Matrix.GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
  exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)

theorem exists_finite_fix {φ : UA E a → ℂ} (hφ : IsAutFormU φ) :
    ∃ t : Finset (HeightOneSpectrum (𝓞 E)), ∀ k ∈ finU (E := E) (n := a), (∀ u, cLoc u k ∈ GlobalTheory.LFun.KGL u (n := a)) →
      (∀ u ∈ t, cLoc u k = 1) → RU E a k φ = φ := by
  haveI : ∀ u : HeightOneSpectrum (𝓞 E), T2Space (GL (Fin a) (u.adicCompletion E)) := fun u =>
    Units.isEmbedding_embedProduct.t2Space
  have hc := (isCompact_integral (E := E) (a := a)).diff hφ.level
  have hcov : {k : finU (E := E) (n := a) | ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a)} \ {k : finU (E := E) (n := a) | RU E a k φ = φ} ⊆
      ⋃ u, {k : finU (E := E) (n := a) | cLoc u k.1 ≠ 1} := by
    rintro k ⟨-, hk⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hne
    push_neg at hne
    apply hk
    show RU E a k.1 φ = φ
    rw [eq_one_of_forall_cLoc k.2 hne, map_one]
    rfl
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover _ (fun u => isOpen_ne_fun
    ((GlobalTheory.BCT.GlobLev.continuous_cLoc u).comp continuous_subtype_val) continuous_const) hcov
  refine ⟨t, fun k hk hint h1 => ?_⟩
  by_contra hne
  have := ht (show (⟨k, hk⟩ : finU (E := E) (n := a)) ∈ _ from ⟨hint, hne⟩)
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
  obtain ⟨u, hu, hne'⟩ := this
  exact hne' (h1 u hu)

theorem one_of_cLoc_eq_one {q : HeightOneSpectrum (𝓞 E)} {z : UA E a} (h : cLoc q z = 1) :
    ∀ u, ¬ Apart u q → cLoc u z = 1 := by
  intro u hu
  by_cases hq : IsSplitAt q
  · exact GlobalTheory.Cong.LevelExt.one_of_cLoc hq z h u hu
  · rw [eq_of_not_apart_of_not_split hq hu]
    exact h

theorem peel (φ : UA E a → ℂ) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ k ∈ finU (E := E) (n := a), (∀ u, cLoc u k ∈ GlobalTheory.LFun.KGL u (n := a)) → (∀ u ∈ S, cLoc u k = 1) → RU E a k φ = φ)
    (Q : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ x ∈ finU (E := E) (n := a), (∀ u, (∀ q ∈ Q, Apart u q) → (u ∈ S → cLoc u x = 1) ∧ cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a)) →
      (∀ q ∈ Q, ∃ y ∈ locU a q, RU E a y φ = φ ∧ cLoc q y = cLoc q x) → RU E a x φ = φ := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro x hx h1 _
    exact hS x hx (fun u => (h1 u (by simp)).2) (fun u hu => (h1 u (by simp)).1 hu)
  | @insert q Q hqQ ih =>
    intro x hx h1 h2
    obtain ⟨y, hyl, hyφ, hyq⟩ := h2 q (Finset.mem_insert_self q Q)
    have hyf : y ∈ finU (E := E) (n := a) := ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).1
    have hya : ∀ u, Apart u q → cLoc u y = 1 := ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).2
    have hq1 : cLoc q (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyq, inv_mul_cancel]
    have hfib : ∀ u, ¬ Apart u q → cLoc u (y⁻¹ * x) = 1 := one_of_cLoc_eq_one hq1
    have happ : ∀ u, Apart u q → cLoc u (y⁻¹ * x) = cLoc u x := fun u hu => by
      rw [map_mul, map_inv, hya u hu, inv_one, one_mul]
    have key : RU E a (y⁻¹ * x) φ = φ := by
      refine ih (y⁻¹ * x) (mul_mem (inv_mem hyf) hx) (fun u hu => ?_) (fun q' hq' => ?_)
      · by_cases huq : Apart u q
        · rw [happ u huq]
          exact h1 u (fun p hp => by
            rcases Finset.mem_insert.1 hp with rfl | hp
            · exact huq
            · exact hu p hp)
        · rw [hfib u huq]
          exact ⟨fun _ => rfl, Subgroup.one_mem _⟩
      · by_cases hqq : Apart q' q
        · obtain ⟨y', hy'l, hy'φ, hy'q⟩ := h2 q' (Finset.mem_insert_of_mem hq')
          exact ⟨y', hy'l, hy'φ, hy'q.trans (happ q' hqq).symm⟩
        · exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl, by rw [map_one, hfib q' hqq]⟩
    have hxe : x = y * (y⁻¹ * x) := by rw [mul_inv_cancel_left]
    rw [hxe, map_mul, Module.End.mul_apply, key, hyφ]

end GlobalTheory.Cong.AdaptLevFix


open GlobalTheory.Cong.AdaptLevFix in
theorem GlobalTheory.Cong.AdaptLev.fixed_of_levelOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → ∀ φ : UA E a → ℂ, IsAutFormU φ → (∀ w, Apart w w₀ → ∀ x ∈ H w, RU E a x φ = φ) → ∀ x ∈ GlobalTheory.Cong.AdaptLev.levelOf a w₀ H, RU E a x φ = φ := by
  intro E _ _ _ a w₀ H hHle _ _ _ hcof φ hφ hfix x hx
  classical
  obtain ⟨t, ht⟩ := exists_finite_fix hφ
  have hT : {w | ¬ H w = intU a w}.Finite := Filter.eventually_cofinite.1 hcof
  let Q : Finset (HeightOneSpectrum (𝓞 E)) := (t ∪ hT.toFinset).filter (fun w => Apart w w₀)
  obtain ⟨hxf, hx1, hxH⟩ := mem_levelOf.1 hx
  refine peel φ (t : Set _) (fun k hk hi h1 => ht k hk hi h1) Q x hxf (fun u hu => ?_) (fun q hq => ?_)
  · by_cases hu0 : Apart u w₀
    · have huQ : u ∉ Q := fun h => hu u h rfl
      have hut : u ∉ t := fun h => huQ (Finset.mem_filter.2 ⟨Finset.mem_union_left _ h, hu0⟩)
      have huT : H u = intU a u := by
        by_contra h
        exact huQ (Finset.mem_filter.2 ⟨Finset.mem_union_right _ (hT.mem_toFinset.2 h), hu0⟩)
      obtain ⟨y, hy, hyx⟩ := hxH u hu0
      rw [huT] at hy
      refine ⟨fun h => absurd h hut, ?_⟩
      rw [← hyx]
      exact (mem_intU.1 hy).2 u (fun h => h rfl)
    · rw [hx1 u hu0]
      exact ⟨fun _ => rfl, Subgroup.one_mem _⟩
  · have hq0 : Apart q w₀ := (Finset.mem_filter.1 hq).2
    obtain ⟨y, hy, hyx⟩ := hxH q hq0
    exact ⟨y, hHle q hy, hfix q hq0 y hy, hyx⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FixedOfFixedByLocalLevelsStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_of_fixed_by_local_levels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → ∀ φ : UA E a → ℂ, IsAutFormU φ → (∀ w, Apart w w₀ → ∀ x ∈ H w, RU E a x φ = φ) → ∀ x ∈ GlobalTheory.Cong.AdaptLev.levelOf a w₀ H, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.AdaptLev.fixed_of_levelOf) | (exact GlobalTheory.Cong.AdaptLev.fixed_of_levelOf) | (intros; apply GlobalTheory.Cong.AdaptLev.fixed_of_levelOf  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLevelAwayDefiniteUnitaryLevelFromLocalLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLevelAwayDefiniteUnitaryLevelFromLocalLevels
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong.LevAway

open Matrix GlobalTheory.PRep Formalism.UG GlobalTheory.BCT GlobalTheory.SplitPts GroundTheory.Automorphic GlobalTheory.BCT.GlobLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem integral_iff (x : UA E a) :
    GeneralLinearGroup.map (pFin E) (x : GA E a) ∈ AdelicGLn.integralFiniteGL E a ↔
      ∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rw [AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem exists_compact_integral : ∃ C : Set (UA E a), IsCompact C ∧
    ∀ x ∈ finU (E := E) (n := a), (∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a)) → x ∈ C := by
  let Kf : Subgroup (finU (E := E) (n := a)) := (AdelicGLn.integralFiniteGL E a).comap (finPart E a)
  have hO : IsOpen (Kf : Set (finU (E := E) (n := a))) := (AdelicGLn.isOpen_integralFiniteGL E a).preimage continuous_finPart
  have hc : IsCompact (Kf : Set (finU (E := E) (n := a))) := by
    refine IsCompact.of_isClosed_subset (isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad))
      (Subgroup.isClosed_of_isOpen _ hO) fun x hx => ⟨finPart E a x, hx, ?_⟩
    have h1 : GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  refine ⟨Subtype.val '' (Kf : Set (finU (E := E) (n := a))), hc.image continuous_subtype_val, fun x hx hi => ⟨⟨x, hx⟩, ?_, rfl⟩⟩
  exact (integral_iff x).2 hi

theorem exists_loc (w : HeightOneSpectrum (𝓞 E)) : ∃ f : UA E a → UA E a, Continuous f ∧
    ∀ x, f x ∈ locU a w ∧ cLoc w (f x) = cLoc w x := by
  by_cases hw : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
    refine ⟨fun x => (e.symm (cLoc w x)).1, continuous_subtype_val.comp (e.symm.continuous.comp (continuous_cLoc w)),
      fun x => ⟨(e.symm _).2, ?_⟩⟩
    rw [← he]; exact e.apply_symm_apply _
  · have hc : conjSrc (conjE E) w = w := conjSrc_eq_of_not_split hw
    have key : ∀ x : UA E a, finGL E a (locGL E a w (cLoc w x)) ∈ UA E a := by
      intro x
      refine finGL_mem_UA _ fun u => ?_
      by_cases hu : u = w
      · subst hu
        have e1 : ∀ v, v = u → GeneralLinearGroup.map (pLoc E v) (locGL E a u (cLoc u x)) = cLoc v x := by
          rintro v rfl; exact pLoc_locGL _ _
        rw [e1 _ hc, e1 u rfl]
        exact comp_eq x u
      · have h3 : conjSrc (conjE E) u ≠ w := fun e => hu (by rw [← conjSrc_conjSrc_cm u, e, hc])
        rw [pLoc_locGL_of_ne hu, pLoc_locGL_of_ne h3]
        simp
    refine ⟨fun x => ⟨finGL E a (locGL E a w (cLoc w x)), key x⟩, ?_, fun x => ⟨?_, ?_⟩⟩
    · exact Continuous.subtype_mk (continuous_finGL_ad.comp ((CuspSub.continuous_locGL w).comp (continuous_cLoc w))) _
    · refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (pInf_finGL _), Subgroup.mem_iInf.2 fun u =>
        Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
      rw [cLoc_finGL]
      exact pLoc_locGL_of_ne (fun e => hu (by rw [e])) _
    · rw [cLoc_finGL]; exact pLoc_locGL _ _

theorem isClosed_finU : IsClosed ((finU (E := E) (n := a) : Subgroup (UA E a)) : Set (UA E a)) := by
  haveI : T2Space (GL (Fin a) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
  have hc : Continuous (cInf (E := E) (n := a)) :=
    (Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_ad)).comp continuous_subtype_val
  exact isClosed_eq hc continuous_const

theorem t2GL (w : HeightOneSpectrum (𝓞 E)) : T2Space (GL (Fin a) (w.adicCompletion E)) :=
  Units.isEmbedding_embedProduct.t2Space

theorem isClosed_levelOf (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a))
    (hc : ∀ w, IsCompact (H w : Set (UA E a))) : IsClosed (levelOf a w₀ H : Set (UA E a)) := by
  have e : (levelOf a w₀ H : Set (UA E a)) = (finU (E := E) (n := a) : Set (UA E a)) ∩
      ((⋂ u, ⋂ (_ : ¬ Apart u w₀), {x | cLoc u x = 1}) ∩
        ⋂ w, ⋂ (_ : Apart w w₀), cLoc w ⁻¹' (cLoc w '' (H w : Set (UA E a)))) := by
    ext x
    simp only [SetLike.mem_coe, mem_levelOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_image]
  rw [e]
  refine isClosed_finU.inter (IsClosed.inter (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    (isClosed_iInter fun w => isClosed_iInter fun _ => ?_))
  · haveI := t2GL (E := E) (a := a) u
    exact isClosed_eq (continuous_cLoc u) continuous_const
  · haveI := t2GL (E := E) (a := a) w
    exact ((hc w).image (continuous_cLoc w)).isClosed.preimage (continuous_cLoc w)

theorem exists_compact_of_finset (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)) (hle : ∀ w, H w ≤ locU a w)
    (hc : ∀ w, IsCompact (H w : Set (UA E a))) (R : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ C : Set (UA E a), IsCompact C ∧ ∀ x ∈ finU (E := E) (n := a), (∀ u, (∀ r ∈ R, Apart u r) → cLoc u x ∈ GlobalTheory.LFun.KGL u (n := a)) →
      (∀ r ∈ R, ∃ y ∈ H r, cLoc r y = cLoc r x) → x ∈ C := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    obtain ⟨C, hC, hsub⟩ := exists_compact_integral (E := E) (a := a)
    exact ⟨C, hC, fun x hx hi _ => hsub x hx fun u => hi u (by simp)⟩
  | insert r R hr ih =>
    obtain ⟨C, hC, hsub⟩ := ih
    refine ⟨C * (H r : Set (UA E a)), hC.mul (hc r), fun x hx hi hH => ?_⟩
    obtain ⟨y, hy, hyx⟩ := hH r (Finset.mem_insert_self r R)
    by_cases hap : ∀ r' ∈ R, Apart r' r
    · have hyl := hle r hy
      have hy1 : ∀ u, Apart u r → cLoc u y = 1 := fun u hu => ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 hyl).2 u hu
      have hyf : y ∈ finU (E := E) (n := a) := (Subgroup.mem_inf.1 hyl).1
      refine ⟨x * y⁻¹, hsub _ (mul_mem hx (inv_mem hyf)) ?_ ?_, y, hy, inv_mul_cancel_right x y⟩
      · intro u hu
        by_cases hur : Apart u r
        · rw [map_mul, map_inv, hy1 u hur, inv_one, mul_one]
          refine hi u fun r' hr' => ?_
          rcases Finset.mem_insert.1 hr' with rfl | h
          · exact hur
          · exact hu r' h
        · have hz : cLoc r (x * y⁻¹) ∈ GlobalTheory.LFun.KGL r (n := a) := by
            rw [map_mul, map_inv, hyx, mul_inv_cancel]; exact one_mem _
          rcases eq_or_eq_conjSrc (not_not.1 hur) with rfl | rfl
          · exact hz
          · exact integral_conjSrc _ r hz
      · intro r' h
        obtain ⟨y', hy', e'⟩ := hH r' (Finset.mem_insert_of_mem h)
        exact ⟨y', hy', by rw [map_mul, map_inv, hy1 r' (hap r' h), inv_one, mul_one]; exact e'⟩
    · push_neg at hap
      obtain ⟨r', hr', hnr⟩ := hap
      have hxC : x ∈ C := by
        refine hsub x hx (fun u hu => hi u fun r'' hr'' => ?_) (fun r'' h => hH r'' (Finset.mem_insert_of_mem h))
        rcases Finset.mem_insert.1 hr'' with rfl | h
        · intro hh
          exact not_apart_trans (not_not.2 hh) (not_apart_symm hnr) (hu r' hr')
        · exact hu r'' h
      exact ⟨x, hxC, 1, one_mem _, mul_one x⟩

theorem isLevelAway_levelOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → IsLevelAway w₀ (GlobalTheory.Cong.AdaptLev.levelOf a w₀ H) := by
  intro E _ _ _ a w₀ H hle _ hc ho hcof
  have hT := Filter.eventually_cofinite.1 hcof
  refine ⟨levelOf_le_finU w₀ H, fun x hx => (mem_levelOf.1 hx).2.1, ?_, ?_⟩
  · obtain ⟨C, hC, hsub⟩ := exists_compact_of_finset H hle hc hT.toFinset
    refine hC.of_isClosed_subset (isClosed_levelOf w₀ H hc) fun x hx => ?_
    obtain ⟨hf, h1, hw⟩ := mem_levelOf.1 hx
    refine hsub x hf (fun u hu => ?_) (fun r _ => ?_)
    · have hHu : H u = intU a u := by
        by_contra h
        exact hu u (hT.mem_toFinset.2 h) rfl
      by_cases h0 : Apart u w₀
      · obtain ⟨y, hy, e⟩ := hw u h0
        rw [hHu] at hy
        rw [← e]
        exact (mem_intU.1 hy).2 u (fun h => h rfl)
      · rw [h1 u h0]; exact one_mem _
    · by_cases h0 : Apart r w₀
      · exact hw r h0
      · exact ⟨1, one_mem _, by rw [map_one, h1 r h0]⟩
  · choose f hfc hf using fun w => exists_loc (E := E) (a := a) w
    let g : ∀ w, UA E a → locU a w := fun w x => ⟨f w x, (hf w x).1⟩
    have hg : ∀ w, Continuous (g w) := fun w => (hfc w).subtype_mk _
    have hpf : Continuous fun x : UA E a => GeneralLinearGroup.map (pFin E) (x : GA E a) :=
      (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp
        continuous_subtype_val
    refine ⟨{x | GeneralLinearGroup.map (pFin E) (x : GA E a) ∈ AdelicGLn.integralFiniteGL E a} ∩
      ⋂ w ∈ hT.toFinset, g w ⁻¹' ((H w).subgroupOf (locU a w) : Set (locU a w)), ?_, ?_, ?_⟩
    · exact ((AdelicGLn.isOpen_integralFiniteGL E a).preimage hpf).inter
        (isOpen_biInter_finset fun w _ => (ho w).preimage (hg w))
    · refine ⟨(integral_iff 1).2 fun u => by rw [map_one]; exact one_mem _, Set.mem_iInter₂.2 fun w _ => ?_⟩
      have h1 : f w 1 = 1 := eq_one_of_cLoc_eq_one (hf w 1).1 (by rw [(hf w 1).2, map_one])
      show (g w 1).1 ∈ H w
      show f w 1 ∈ H w
      rw [h1]; exact one_mem _
    · intro x hxN hxf hx1
      obtain ⟨hxi, hxH⟩ := hxN
      have hxi' := (integral_iff x).1 hxi
      refine mem_levelOf.2 ⟨hxf, hx1, fun w _ => ⟨f w x, ?_, (hf w x).2⟩⟩
      by_cases hwT : H w = intU a w
      · rw [hwT]; exact mem_intU_of (hf w x).1 (by rw [(hf w x).2]; exact hxi' w)
      · exact Set.mem_iInter₂.1 hxH w (hT.mem_toFinset.2 hwT)

end GlobalTheory.Cong.LevAway
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLevelAwayDefiniteUnitaryLevelFromLocalLevelsStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevelAway_definiteUnitaryLevelFromLocalLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w₀ : HeightOneSpectrum (𝓞 E)) (H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, H w ≤ locU a w) → (∀ w u, ¬ Apart w u → H w = H u) → (∀ w, IsCompact (H w : Set (UA E a))) → (∀ w, IsOpen (((H w).subgroupOf (locU a w)) : Set (locU a w))) → (∀ᶠ w in Filter.cofinite, H w = GlobalTheory.Cong.AdaptLev.intU a w) → IsLevelAway w₀ (GlobalTheory.Cong.AdaptLev.levelOf a w₀ H) := by
  first | (exact @GlobalTheory.Cong.LevAway.isLevelAway_levelOf) | (exact GlobalTheory.Cong.LevAway.isLevelAway_levelOf) | (intros; apply GlobalTheory.Cong.LevAway.isLevelAway_levelOf  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorFixedByProductLocalLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorFixedByProductLocalLevels
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.FixProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem rU_mul (x y : UA E a) (f : UA E a → ℂ) : RU E a (x * y) f = RU E a x (RU E a y f) := by
  rw [map_mul]; rfl

theorem locU_le_finU (w : HeightOneSpectrum (𝓞 E)) : locU a w ≤ finU (E := E) (n := a) :=
  fun _ hx => (Subgroup.mem_inf.1 hx).1

theorem commute_of_apart {w u : HeightOneSpectrum (𝓞 E)} (h : Apart w u) {x y : UA E a}
    (hx : x ∈ locU a w) (hy : y ∈ locU a u) : Commute x y := by
  show x * y = y * x
  refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun v => ?_)
  · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_inf hx, GlobalTheory.DefU.LocRet.mem_locU_inf hy]
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · have hv' : v.under (𝓞 (maximalRealSubfield E)) ≠ u.under (𝓞 (maximalRealSubfield E)) := hv ▸ h
      simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hy hv', one_mul, mul_one]
    · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hx hv, one_mul, mul_one]

section Avg

variable (K : Subgroup (UA E a)) (K' : Subgroup K) [Fintype (K ⧸ K')]

def avg : (UA E a → ℂ) →ₗ[ℂ] (UA E a → ℂ) :=
  ∑ q : K ⧸ K', RU E a ((Quotient.out q : K) : UA E a)

theorem avg_apply (f : UA E a → ℂ) :
    avg K K' f = ∑ q : K ⧸ K', RU E a ((Quotient.out q : K) : UA E a) f := by
  unfold avg
  exact LinearMap.sum_apply _ _ _

theorem avg_comm {c : UA E a} (hc : ∀ k ∈ K, Commute c k) (f : UA E a → ℂ) :
    avg K K' (RU E a c f) = RU E a c (avg K K' f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_apply, avg_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← rU_mul, ← rU_mul, (hc _ (Quotient.out q).2).eq]

theorem avg_of_fixed {f : UA E a → ℂ} (hf : ∀ k ∈ K, RU E a k f = f) :
    avg K K' f = (Fintype.card (K ⧸ K') : ℂ) • f := by
  rw [avg_apply, Finset.sum_congr rfl (fun q _ => hf _ (Quotient.out q).2), Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem avg_fixed {f : UA E a → ℂ} (hf : ∀ k ∈ K', RU E a ((k : K) : UA E a) f = f) (k : UA E a) (hk : k ∈ K) :
    RU E a k (avg K K' f) = avg K K' f := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_apply, map_sum]
  have key : ∀ q : K ⧸ K', RU E a k (RU E a ((Quotient.out q : K) : UA E a) f) =
      RU E a ((Quotient.out ((⟨k, hk⟩ : K) • q) : K) : UA E a) f := by
    intro q
    have hm : (Quotient.out ((⟨k, hk⟩ : K) • q))⁻¹ * ((⟨k, hk⟩ : K) * Quotient.out q) ∈ K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have e : (⟨k, hk⟩ : K) * Quotient.out q = Quotient.out ((⟨k, hk⟩ : K) • q) *
        ((Quotient.out ((⟨k, hk⟩ : K) • q))⁻¹ * ((⟨k, hk⟩ : K) * Quotient.out q)) := (mul_inv_cancel_left _ _).symm
    have e' := congrArg (fun z : K => (z : UA E a)) e
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at e'
    have hm' := hf _ hm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at hm'
    rw [← rU_mul, e', rU_mul, hm']
  rw [Finset.sum_congr rfl fun q _ => key q]
  exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ (fun q => rfl)

end Avg

theorem mend (U : Submodule ℂ (UA E a → ℂ)) (hU : IsAutRepU U) (w : HeightOneSpectrum (𝓞 E))
    (K : Subgroup (UA E a)) (hKw : K ≤ locU a w) (hKc : IsCompact (K : Set (UA E a)))
    {φw : UA E a → ℂ} (hφwU : φw ∈ U) (hφw0 : φw ≠ 0) (hφwK : ∀ k ∈ K, RU E a k φw = φw)
    {φ : UA E a → ℂ} (hφU : φ ∈ U) (hφ0 : φ ≠ 0) :
    ∃ ψ ∈ U, ψ ≠ 0 ∧ (∀ k ∈ K, RU E a k ψ = ψ) ∧
      ∀ y : UA E a, (∀ x ∈ locU a w, Commute y x) → RU E a y φ = φ → RU E a y ψ = ψ := by
  classical

  let S := Submodule.span ℂ (Set.range fun g : UA E a => RU E a g φ)
  have hSU : S ≤ U := Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact hU.stable g φ hφU)
  have hSst : ∀ x, ∀ f ∈ S, RU E a x f ∈ S := by
    intro x f hf
    have : S ≤ S.comap (RU E a x) := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      show RU E a x (RU E a g φ) ∈ S
      rw [← rU_mul]
      exact Submodule.subset_span ⟨_, rfl⟩)
    exact this hf
  have hφS : φ ∈ S := by
    have h1 : RU E a 1 φ = φ := by rw [map_one]; rfl
    rw [← h1]
    exact Submodule.subset_span ⟨1, rfl⟩
  have hSeq : S = U := by
    rcases hU.irred S hSU hSst with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hφS)) hφ0
    · exact h
  have hφwS : φw ∈ S := hSeq ▸ hφwU
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hφwS

  let r : UA E a → UA E a := fun g => (GlobalTheory.DefU.LocRet.ret w a g : UA E a)
  have hr : ∀ g, r g ∈ locU a w := fun g => (GlobalTheory.DefU.LocRet.ret w a g).2
  have hd : ∀ g, ∀ x ∈ locU a w, Commute ((r g)⁻¹ * g) x := fun g x hx =>
    GlobalTheory.DefU.LocRet.commute_ret g ⟨x, hx⟩
  have hsplit : ∀ g, RU E a g φ = RU E a ((r g)⁻¹ * g) (RU E a (r g) φ) := by
    intro g
    rw [← rU_mul, (hd g (r g) (hr g)).eq, mul_inv_cancel_left]

  have hKf : K ≤ finU (E := E) (n := a) := hKw.trans (locU_le_finU w)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  let K' : Subgroup K :=
    { carrier := {k | ∀ g ∈ c.support, RU E a (k : UA E a) (RU E a (r g) φ) = RU E a (r g) φ}
      mul_mem' := fun {x y} hx hy g hg => by
        show RU E a ((x : UA E a) * (y : UA E a)) _ = _
        rw [rU_mul, hy g hg, hx g hg]
      one_mem' := fun g _ => by
        show RU E a 1 _ = _
        rw [map_one]; rfl
      inv_mem' := fun {x} hx g hg => by
        have h := hx g hg
        show RU E a ((x : UA E a)⁻¹) _ = _
        calc _ = RU E a ((x : UA E a)⁻¹) (RU E a (x : UA E a) (RU E a (r g) φ)) := by rw [h]
          _ = _ := by rw [← rU_mul, inv_mul_cancel, map_one]; rfl }
  have hK'o : IsOpen (K' : Set K) := by
    have e : (K' : Set K) =
        ⋂ g ∈ c.support, {k : K | RU E a (k : UA E a) (RU E a (r g) φ) = RU E a (r g) φ} := by
      ext k
      rw [Set.mem_iInter₂]
      rfl
    rw [e]
    refine isOpen_biInter_finset fun g _ => ?_
    have ho := (hU.aut _ (hU.stable (r g) φ hφU)).level
    have hcont : Continuous fun k : K => (⟨(k : UA E a), hKf k.2⟩ : finU (E := E) (n := a)) :=
      continuous_subtype_val.subtype_mk _
    exact ho.preimage hcont
  haveI : Finite (K ⧸ K') := Subgroup.quotient_finite_of_isOpen K' hK'o
  letI : Fintype (K ⧸ K') := Fintype.ofFinite _
  have hA : avg K K' φw = c.sum fun g b => b • RU E a ((r g)⁻¹ * g) (avg K K' (RU E a (r g) φ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, Finsupp.sum, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, hsplit g, avg_comm K K' (fun k hk => hd g k (hKw hk))]
  by_cases h0 : ∀ g ∈ c.support, avg K K' (RU E a (r g) φ) = 0
  · exfalso
    have hz : avg K K' φw = 0 := by
      rw [hA, Finsupp.sum]
      exact Finset.sum_eq_zero fun g hg => by rw [h0 g hg, map_zero, smul_zero]
    rw [avg_of_fixed K K' hφwK] at hz
    have hcard : (Fintype.card (K ⧸ K') : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨(QuotientGroup.mk 1 : K ⧸ K')⟩).ne'
    exact hφw0 ((smul_eq_zero.1 hz).resolve_left hcard)
  · push_neg at h0
    obtain ⟨g, hg, hne⟩ := h0
    refine ⟨avg K K' (RU E a (r g) φ), ?_, hne, ?_, ?_⟩
    · rw [avg_apply]
      exact Submodule.sum_mem _ fun q _ => hU.stable _ _ (hU.stable _ _ hφU)
    · exact avg_fixed K K' (fun k hk => hk g hg)
    · intro y hy hyφ
      rw [← avg_comm K K' (fun k hk => hy k (hKw hk)), ← rU_mul, (hy (r g) (hr g)).eq, rU_mul, hyφ]

theorem fix_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (K : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, K w ≤ locU a w) → (∀ w u, ¬ Apart w u → K w = K u) → (∀ w, IsCompact (K w : Set (UA E a))) → (∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) → (∀ w, IsOpen ((K w).subgroupOf (locU a w) : Set (locU a w))) → (∀ w, Apart w w₀ → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K w, RU E a x φ = φ) → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ w, Apart w w₀ → ∀ x ∈ K w, RU E a x φ = φ := by
  intro E _ _ _ a U hU w₀ K hKl hKeq hKc hKint _ hφ'
  classical
  obtain ⟨φ₀, hφ₀U, hφ₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU (E := E) (n := a)) :=
    { carrier := {k | RU E a (k : UA E a) φ₀ = φ₀}
      mul_mem' := fun {x y} hx hy => by
        show RU E a ((x : UA E a) * (y : UA E a)) φ₀ = φ₀
        rw [rU_mul]
        exact (congrArg _ hy).trans hx
      one_mem' := by
        show RU E a 1 φ₀ = φ₀
        rw [map_one]; rfl
      inv_mem' := fun {x} hx => by
        show RU E a ((x : UA E a)⁻¹) φ₀ = φ₀
        have hx' : RU E a (x : UA E a) φ₀ = φ₀ := hx
        calc _ = RU E a ((x : UA E a)⁻¹) (RU E a (x : UA E a) φ₀) := by rw [hx']
          _ = _ := by rw [← rU_mul, inv_mul_cancel, map_one]; rfl }
  have hLo : IsOpen (L : Set (finU (E := E) (n := a))) := (hU.aut φ₀ hφ₀U).level
  have hev := GlobalTheory.BCT.GlobLev.eventually_locU_mem E a L hLo
  have hgood : ∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, RU E a x φ₀ = φ₀ := by
    filter_upwards [hev, hKint] with w h1 h2 x hx
    exact h1 x (hKl w hx) (h2 x hx) (locU_le_finU w (hKl w hx))
  have hB := Filter.eventually_cofinite.1 hgood
  have main : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), ∃ φ ∈ U, φ ≠ 0 ∧ ∀ u, Apart u w₀ →
      ((∀ x ∈ K u, RU E a x φ₀ = φ₀) ∨ u ∈ S) → ∀ x ∈ K u, RU E a x φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨φ₀, hφ₀U, hφ₀, fun u _ hu x hx => ?_⟩
      rcases hu with hu | hu
      · exact hu x hx
      · exact absurd hu (Finset.notMem_empty u)
    | insert w S hwS ih =>
      obtain ⟨φ, hφU, hφ0, hφ⟩ := ih
      by_cases hw : Apart w w₀
      · obtain ⟨φw, hφwU, hφw0, hφwK⟩ := hφ' w hw
        obtain ⟨ψ, hψU, hψ0, hψK, hψy⟩ := mend U hU w (K w) (hKl w) (hKc w) hφwU hφw0 hφwK hφU hφ0
        refine ⟨ψ, hψU, hψ0, fun u hu hu' x hx => ?_⟩
        by_cases hap : Apart u w
        · refine hψy x (fun z hz => commute_of_apart hap (hKl u hx) hz) ?_
          rcases hu' with h | h
          · exact hφ u hu (Or.inl h) x hx
          · rcases Finset.mem_insert.1 h with rfl | h
            · exact absurd rfl hap
            · exact hφ u hu (Or.inr h) x hx
        · rw [hKeq u w hap] at hx
          exact hψK x hx
      · refine ⟨φ, hφU, hφ0, fun u hu hu' x hx => ?_⟩
        rcases hu' with h | h
        · exact hφ u hu (Or.inl h) x hx
        · rcases Finset.mem_insert.1 h with rfl | h
          · exact absurd hu hw
          · exact hφ u hu (Or.inr h) x hx
  obtain ⟨φ, hφU, hφ0, hφ⟩ := main hB.toFinset
  refine ⟨φ, hφU, hφ0, fun u hu x hx => hφ u hu ?_ x hx⟩
  by_cases h : ∀ x ∈ K u, RU E a x φ₀ = φ₀
  · exact Or.inl h
  · exact Or.inr (hB.mem_toFinset.2 h)

end GlobalTheory.Cong.FixProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorFixedByProductLocalLevelsStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vector_fixed_by_product_localLevels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (K : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)), (∀ w, K w ≤ locU a w) → (∀ w u, ¬ Apart w u → K w = K u) → (∀ w, IsCompact (K w : Set (UA E a))) → (∀ᶠ w in Filter.cofinite, ∀ x ∈ K w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a)) → (∀ w, IsOpen ((K w).subgroupOf (locU a w) : Set (locU a w))) → (∀ w, Apart w w₀ → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ K w, RU E a x φ = φ) → ∃ φ ∈ U, φ ≠ 0 ∧ ∀ w, Apart w w₀ → ∀ x ∈ K w, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.FixProd.fix_prod) | (exact GlobalTheory.Cong.FixProd.fix_prod) | (intros; apply GlobalTheory.Cong.FixProd.fix_prod  <;> assumption)
end
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem apart_of_apart_not_apart {w w₀ u : HeightOneSpectrum (𝓞 E)} (hw : Apart w w₀) (hu : ¬ Apart u w₀) : Apart u w := by
  unfold Apart at *
  intro h
  exact hw (h.symm.trans (not_not.1 hu))

theorem mem_levelOf_iff_of_locU {w₀ w : HeightOneSpectrum (𝓞 E)} {H : HeightOneSpectrum (𝓞 E) → Subgroup (UA E a)}
    (hle : ∀ w, H w ≤ locU a w) (hfib : ∀ w u, ¬ Apart w u → H w = H u) (hw : Apart w w₀) {x : UA E a}
    (hx : x ∈ locU a w) : x ∈ levelOf a w₀ H ↔ x ∈ H w := by
  have hx' := (GlobalTheory.Cong.LevelExt.mem_locU_iff x).1 hx
  constructor
  · intro h
    obtain ⟨y, hy, e⟩ := (mem_levelOf.1 h).2.2 w hw
    rw [← eq_of_cLoc_eq (hle w hy) hx e]
    exact hy
  · intro h
    refine mem_levelOf.2 ⟨hx'.1, fun u hu => hx'.2 u (apart_of_apart_not_apart hw hu), fun w' hw' => ?_⟩
    by_cases hw'w : Apart w' w
    · exact ⟨1, one_mem _, by rw [map_one, hx'.2 w' hw'w]⟩
    · exact ⟨x, by rw [hfib w' w hw'w]; exact h, rfl⟩

theorem map_eq_image {w : HeightOneSpectrum (𝓞 E)} {L : Subgroup (UA E a)} (hL : L ≤ locU a w)
    (e : locU a w ≃ₜ* GL (Fin a) (w.adicCompletion E)) (he : ∀ x : locU a w, e x = cLoc w (x : UA E a)) :
    ((L.map (cLoc w) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) =
      e '' ((L.subgroupOf (locU a w) : Subgroup (locU a w)) : Set (locU a w)) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hL hx⟩, Subgroup.mem_subgroupOf.2 hx, he _⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, Subgroup.mem_subgroupOf.1 hy, (he y).symm⟩

theorem injective_of_compAlong {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    (hirr : σ.IsIrreducible) (f : W →ₗ[ℂ] (UA E a → ℂ)) (hf0 : f ≠ 0)
    (hf : ∀ (x : locU a w) v, f (σ (((cLoc w).comp (locU a w).subtype) x) v) = RU E a x (f v)) :
    Function.Injective f := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  rw [← LinearMap.ker_eq_bot]
  refine (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hirr).2 _ (fun g u hu => ?_)).resolve_right fun h => hf0 ?_
  · rw [LinearMap.mem_ker] at hu ⊢
    have := hf (e.symm g) u
    have hg : ((cLoc w).comp (locU a w).subtype) (e.symm g) = g := by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← he, e.apply_symm_apply]
    rw [hg] at this
    rw [this, hu, map_zero]
  · refine LinearMap.ext fun v => ?_
    have : v ∈ LinearMap.ker f := h ▸ Submodule.mem_top
    simpa using this

theorem fix_of_fixed {U : Submodule ℂ (UA E a → ℂ)} {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w)
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hc : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ)
    {J : Subgroup (GL (Fin a) (w.adicCompletion E))} (hJ : GlobalTheory.PRep.fixed σ.ρ J ≠ ⊥) :
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w, cLoc w x ∈ J → RU E a x φ = φ := by
  obtain ⟨hirr, f, hf0, hfU, hf⟩ := hc
  have hinj := injective_of_compAlong hw hirr f hf0 hf
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hJ
  refine ⟨f v, hfU v, fun h => hv0 (hinj (by rw [h, map_zero])), fun x hx hxJ => ?_⟩
  have := hf ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, GlobalTheory.LGrp.mem_fixed.1 hv _ hxJ] at this
  exact this.symm

theorem fixed_ne_bot_of_fix {U : Submodule ℂ (UA E a → ℂ)} (hU : IsAutRepU U) {w : HeightOneSpectrum (𝓞 E)}
    (hw : IsSplitAt w) (σ : SmIrr (GL (Fin a) (w.adicCompletion E)))
    (hc : IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ)
    {L : Subgroup (UA E a)} (hL : L ≤ locU a w) {φ : UA E a → ℂ} (hφU : φ ∈ U) (hφ0 : φ ≠ 0)
    (hφ : ∀ x ∈ L, RU E a x φ = φ) : GlobalTheory.PRep.fixed σ.ρ (L.map (cLoc w)) ≠ ⊥ := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  have hp : (cLoc w).comp (locU a w).subtype = e.toMulEquiv.toMonoidHom := MonoidHom.ext fun x => (he x).symm
  have hirr : Representation.IsIrreducible (σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) := by
    rw [hp]; exact GlobalTheory.CuspMult.isIrreducible_comp_mulEquiv σ.ρ e.toMulEquiv σ.irred
  have hsup := GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component E a U hU w hw σ hc φ hφU
  let ι := {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}
  have hf' : ∀ (i : ι) (g : locU a w) (u : σ.V), i.1 ((σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) g u) =
      ((RU E a).comp (locU a w).subtype) g (i.1 u) := fun i g u => i.2.2 g u
  have hK : ∀ k ∈ {x : locU a w | (x : UA E a) ∈ L}, ((RU E a).comp (locU a w).subtype) k φ = (1 : ℂ) • φ :=
    fun k hk => by rw [one_smul]; exact hφ k.1 hk
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.SplitEigen.exists_eigen_of_mem_iSup (ι := ι) ((RU E a).comp (locU a w).subtype)
    (σ.ρ.comp ((cLoc w).comp (locU a w).subtype)) hirr (fun i => i.1) hf'
    {x : locU a w | (x : UA E a) ∈ L} (fun _ => 1) φ hφ0 hK hsup
  refine (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 ?_, hv0⟩
  rintro _ ⟨x, hx, rfl⟩
  have := hv ⟨x, hL hx⟩ hx
  rw [one_smul] at this
  exact this

theorem KGL_le_map {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) :
    GlobalTheory.LFun.KGL w (n := a) ≤ (intU a w).map (cLoc w) := by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  intro g hg
  have h1 : cLoc w ((e.symm g : locU a w) : UA E a) = g := by rw [← he, e.apply_symm_apply]
  exact ⟨(e.symm g).1, mem_intU_of (e.symm g).2 (by rw [h1]; exact hg), h1⟩

end GlobalTheory.Cong.AdaptLev

end
