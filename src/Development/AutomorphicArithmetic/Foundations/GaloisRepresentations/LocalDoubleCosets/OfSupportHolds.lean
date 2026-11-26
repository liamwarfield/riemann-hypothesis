module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePowAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.GLFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.ExistsStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.LocDescOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.DistZero
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.distZero :
    CellStep → DistZero := by
  intro hstep X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hcomm χ hχ k x hfix huniq hcl D hD hsum f hf
  obtain ⟨C, hC⟩ : ∃ C : Fin k → Set X, C = fun j => MulAction.orbit H (x j) := ⟨_, rfl⟩
  have hCl : ∀ l y, y ∈ C l ↔ y ∈ MulAction.orbit H (x l) := by
    intro l y
    rw [hC]
  have hcov : ∀ y, ∃ l, y ∈ C l := fun y => ⟨(huniq y).exists.choose, (hCl _ _).mpr (huniq y).exists.choose_spec⟩
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro y hi hj
    exact hij ((huniq y).unique ((hCl _ _).mp hi) ((hCl _ _).mp hj))
  have hcl' : ∀ j, closure (C j) ⊆ ⋃ l, ⋃ (_ : j ≤ l), C l := by
    rw [hC]
    exact hcl
  have hsorb : ∀ l y, y ∈ C l → s y ∈ C l := by
    intro l y hy
    rw [hCl] at hy ⊢
    obtain ⟨g, rfl⟩ := hy
    exact ⟨τ g, by rw [hcomm, hfix]⟩
  have key : ∀ j : ℕ, j ≤ k → ∀ g ∈ GroundTheory.Automorphic.Whittaker.supportedIn (GroundTheory.Automorphic.Parabolic.cellUnion C j), D g = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ g hg
      rw [GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Parabolic.cellUnion_zero] at hg
      have hg0 : g = 0 := by
        funext y
        by_contra hy
        exact hg.2 hy
      rw [hg0, map_zero]
    | succ j ih =>
      intro hjk g hg
      have hj : j < k := by omega
      have hU : GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1) = GroundTheory.Automorphic.Parabolic.cellUnion C ((⟨j, hj⟩ : Fin k) : ℕ) ∪ C ⟨j, hj⟩ :=
        GroundTheory.Automorphic.Parabolic.cellUnion_succ (C := C) ⟨j, hj⟩
      refine hstep X H s τ p hp hs hτ hsp hτp hcomm χ hχ D hD hsum
        (GroundTheory.Automorphic.Parabolic.cellUnion C (j + 1)) (closure (C ⟨j, hj⟩)) (x ⟨j, hj⟩)
        (GroundTheory.Automorphic.Parabolic.isOpen_cellUnion hdisj hcov hcl' (j + 1)) isClosed_closure ?_ ?_ ?_ (hfix _) ?_ g hg
      · rw [Set.inter_comm]
        have h1 := GroundTheory.Automorphic.Parabolic.closure_inter_cellUnion_succ hdisj hcl' ⟨j, hj⟩
        rw [h1, hC]
      · intro h y hy
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion] at hy ⊢
        obtain ⟨l, hl, hyl⟩ := hy
        refine ⟨l, hl, ?_⟩
        rw [hCl] at hyl ⊢
        obtain ⟨g', rfl⟩ := hyl
        exact ⟨h * g', mul_smul _ _ _⟩
      · intro y
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion, GroundTheory.Automorphic.Parabolic.mem_cellUnion]
        constructor
        · rintro ⟨l, hl, hsy⟩
          obtain ⟨m, hm⟩ := hcov y
          have hlm : l = m := (huniq (s y)).unique ((hCl _ _).mp hsy) ((hCl _ _).mp (hsorb m y hm))
          subst hlm
          exact ⟨l, hl, hm⟩
        · rintro ⟨l, hl, hy⟩
          exact ⟨l, hl, hsorb l y hy⟩
      · intro g' hg'
        rw [Submodule.mem_inf, GroundTheory.Automorphic.Whittaker.mem_supportedIn, GroundTheory.Automorphic.Whittaker.mem_vanishingOn] at hg'
        obtain ⟨hg1, hg2⟩ := hg'
        apply ih (by omega)
        rw [GroundTheory.Automorphic.Whittaker.mem_supportedIn]
        refine ⟨hg1.1, ?_⟩
        intro y hy
        have hyU := hg1.2 hy
        rw [GroundTheory.Automorphic.Parabolic.mem_cellUnion] at hyU ⊢
        obtain ⟨l, hl, hyl⟩ := hyU
        refine ⟨l, ?_, hyl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt | heq
        · exact hlt
        · exfalso
          apply hy
          apply hg2
          have hleq : l = ⟨j, hj⟩ := Fin.ext heq
          rw [hleq] at hyl
          exact subset_closure hyl
  apply key k le_rfl f
  rw [GroundTheory.Automorphic.Parabolic.cellUnion_of_cover hcov, GroundTheory.Automorphic.Whittaker.mem_supportedIn]
  exact ⟨hf, Set.subset_univ _⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.FunInv
noncomputable section

open MeasureTheory

namespace UpperTheory.Gal.LocD

section Stable

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem mem_Cc {f : G → ℂ} : f ∈ Cc G ↔ IsLocallyConstant f ∧ HasCompactSupport f :=
  GroundTheory.Automorphic.mem_locallyConstantCompactSupport

private theorem Cc_comp_homeo {f : G → ℂ} (hf : f ∈ Cc G) (e : G ≃ₜ G) : f ∘ e ∈ Cc G := by
  rw [mem_Cc] at hf ⊢
  exact ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

private def homeoOf (s : G →* G) (p : ℕ) (hp : 0 < p) (hs : Continuous s) (hsp : ∀ g, s^[p] g = g) : G ≃ₜ G where
  toFun := s
  invFun := s^[p - 1]
  left_inv g := by
    have : s^[p - 1 + 1] g = g := by rw [Nat.sub_add_cancel hp]; exact hsp g
    rwa [Function.iterate_succ_apply] at this
  right_inv g := by
    have : s^[p - 1 + 1] g = g := by rw [Nat.sub_add_cancel hp]; exact hsp g
    rwa [Function.iterate_succ_apply'] at this
  continuous_toFun := hs
  continuous_invFun := hs.iterate _

end Stable

theorem funInv (hBi : BiInv) (hMem : PrMem) (hLeft : PrLeft) (hAuto : PrAuto) (hSurj : PrSurj) (hEta : EtaEx) :
    FunInv := by
  intro G _ _ _ _ _ _ _ B N hB hN K hKo hKc hBK s p hp hs hsp hsB hsN hC χ θ hχ hθ hχs hθs l hl φ hφ
  letI : MeasurableSpace B := borel B
  haveI : BorelSpace B := ⟨rfl⟩
  haveI : LocallyCompactSpace B := hB.locallyCompactSpace
  set μ : Measure B := Measure.haar with hμ
  obtain ⟨hmem, hadd⟩ := hMem G B hB μ χ hχ
  obtain ⟨f, hf, rfl⟩ := hSurj G B hB μ χ K hKo hKc hBK φ hφ
  by_cases hne : ∃ f ∈ Cc G, ∃ g, pr B μ χ f g ≠ 0
  swap
  · push_neg at hne
    have h0 : pr B μ χ f = 0 := funext (hne f hf)
    rw [h0]
    rfl
  obtain ⟨κ, hκ, hκs⟩ := hAuto G B hB μ χ s p hp hs hsp hsB hχs
  obtain ⟨hκ1, η, hη, hηL, hηs⟩ :=
    hEta G B s p hp hsp (pr B μ χ) κ hκ hκs (fun b => hLeft G B hB μ χ b) hne
  let prL : Cc G →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f => pr B μ χ f
      map_add' := fun f f' => hadd f f.2 f' f'.2
      map_smul' := fun c f => by
        funext g
        simp only [pr, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext b
        ring }
  obtain ⟨q, hq⟩ := (Cc G).exists_isCompl
  let D : (G → ℂ) →ₗ[ℂ] ℂ := l ∘ₗ prL ∘ₗ (Cc G).projectionOnto q hq
  have hDf : ∀ f' (hf' : f' ∈ Cc G), D f' = l (pr B μ χ f') := by
    intro f' hf'
    show l (prL ((Cc G).projectionOnto q hq f')) = _
    rw [show (Cc G).projectionOnto q hq f' = ⟨f', hf'⟩ from
      Submodule.linearProjOfIsCompl_apply_left hq ⟨f', hf'⟩]
    rfl
  have hCs : f ∘ s ∈ Cc G := Cc_comp_homeo hf (homeoOf s p hp hs hsp)
  have hDleft : ∀ (b : B), ∀ f' ∈ Cc G, (D fun x => f' ((b : G)⁻¹ * x)) = η b * D f' := by
    intro b f' hf'
    have hmL : (fun x => f' ((b : G)⁻¹ * x)) ∈ Cc G :=
      Cc_comp_homeo hf' (Homeomorph.mulLeft ((b : G)⁻¹))
    have he : pr B μ χ (fun x => f' ((b : G)⁻¹ * x)) = η b • pr B μ χ f' :=
      funext fun g => hη b f' g
    rw [hDf _ hmL, hDf f' hf', he, map_smul, smul_eq_mul]
  have hDright : ∀ (u : N), ∀ f' ∈ Cc G, (D fun x => f' (x * (u : G))) = (θ u : ℂ) * D f' := by
    intro u f' hf'
    have hmR : (fun x => f' (x * (u : G))) ∈ Cc G :=
      Cc_comp_homeo hf' (Homeomorph.mulRight (u : G))
    have he : pr B μ χ (fun x => f' (x * (u : G))) = fun x => pr B μ χ f' (x * (u : G)) := by
      funext g
      simp only [pr, mul_assoc]
    rw [hDf _ hmR, hDf f' hf', he]
    exact hl u _ (hmem f' hf')
  have hps : pr B μ χ (f ∘ s) = pr B μ χ f ∘ s := by
    funext g
    rw [hκs, hκ1]
    simp
  rw [← hps, ← hDf _ hCs, ← hDf f hf]
  exact hBi G B N hB hN s p hp hs hsp hsB hsN hC η θ hηL hθ hηs hθs D hDleft hDright f hf

end UpperTheory.Gal.LocD

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.Imports
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.eig :
    EigZero → Eig := by
  intro hE T J _ _ _ _ _ ρ s A hA hμs
  obtain ⟨μ, l0, hl0, hl0eq, hgen⟩ := hE T J ρ
  have hμ : ∀ t, μ (s t) = μ t := hμs μ hgen
  let W : Submodule ℂ (Module.Dual ℂ J) :=
    { carrier := {l | ∀ t y, l (ρ t y) = (μ t : ℂ) * l y}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        intro t y
        simp only [LinearMap.add_apply, ha t y, hb t y]
        ring
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro t y
        simp
      smul_mem' := by
        intro c l hl
        simp only [Set.mem_setOf_eq] at *
        intro t y
        simp only [LinearMap.smul_apply, smul_eq_mul, hl t y]
        ring }
  have hAW : ∀ l ∈ W, LinearMap.dualMap A l ∈ W := by
    intro l hl t y
    show l (A (ρ t y)) = (μ t : ℂ) * l (A y)
    rw [hA, hl, hμ]
  let A' : W →ₗ[ℂ] W := (LinearMap.dualMap A).restrict hAW
  haveI : Nontrivial W := ⟨⟨⟨l0, hl0eq⟩, 0, fun h => hl0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A'
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  refine ⟨μ, (v : Module.Dual ℂ J), c, fun h => hv.2 (Subtype.ext h), hμ, v.2, fun y => ?_⟩
  have := congrArg (fun w : W => (w : Module.Dual ℂ J) y) hv.apply_eq_smul
  simpa [A'] using this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.GLCells
noncomputable section

open UpperTheory.ConvolutionTheory.Loc Matrix
open GroundTheory.Automorphic (permGL permGL_apply)
open DoubleCoset (doubleCoset mem_doubleCoset)

namespace UpperTheory.Gal.LocD

section SlopeTestRemainingChoices

variable {E : Type} [Field E] {n : ℕ}

private theorem mem_blockUpper_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ) ↔ g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GroundTheory.Automorphic.Iwasawa.mem_blockUpper, GlobalTheory.SmGL.mem_borel]
  exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩

private theorem mem_autBorel_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.borel n E ↔ g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GroundTheory.Automorphic.mem_borel_iff, GlobalTheory.SmGL.mem_borel E]

private theorem mem_unipotent_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.Iwasawa.unipotent E n ↔ g ∈ GlobalTheory.SmGL.unipB E (Fin n) := by
  rw [GroundTheory.Automorphic.Iwasawa.mem_unipotent, GlobalTheory.SmGL.mem_unipB E]
  exact Iff.rfl

private theorem unipB_le_borel {g : GL (Fin n) E} (hg : g ∈ GlobalTheory.SmGL.unipB E (Fin n)) :
    g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GlobalTheory.SmGL.mem_unipB] at hg
  rw [GlobalTheory.SmGL.mem_borel]
  exact hg.1

private theorem doubleCoset_eq_cell (w : Equiv.Perm (Fin n)) :
    doubleCoset (permGL E w) (GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ) : Set (GL (Fin n) E))
        (GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ)) =
      cell (GlobalTheory.SmGL.borel E (Fin n)) (GlobalTheory.SmGL.unipB E (Fin n)) (permGL E w) := by
  have hset : ((GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ)) : Set (GL (Fin n) E)) =
      ((GroundTheory.Automorphic.Iwasawa.borel E n) : Set (GL (Fin n) E)) := by
    ext g
    simp only [SetLike.mem_coe]
    rw [mem_blockUpper_iff, ← mem_autBorel_iff]
    rfl
  ext g
  constructor
  · intro hg
    rw [hset, GroundTheory.Automorphic.Whittaker.mem_doubleCoset_iff_normalForm] at hg
    obtain ⟨u, hu, t, v, hv, rfl⟩ := hg
    refine ⟨u * GroundTheory.Automorphic.Iwasawa.diagGL E n t, ?_, v, ?_, rfl⟩
    · refine Subgroup.mul_mem _ ?_ ?_
      · exact unipB_le_borel (mem_unipotent_iff.mp hu)
      · exact mem_autBorel_iff.mp (GroundTheory.Automorphic.Whittaker.diagGL_mem_borel t)
    · exact mem_unipotent_iff.mp hv
  · rintro ⟨b, hb, u, hu, rfl⟩
    rw [mem_doubleCoset]
    exact ⟨b, mem_blockUpper_iff.mpr hb, u, mem_blockUpper_iff.mpr (unipB_le_borel hu), rfl⟩

private theorem sg_permGL (σ : E ≃+* E) (w : Equiv.Perm (Fin n)) : sg σ (permGL E w) = permGL E w := by
  ext i j
  rw [sg_val, permGL_apply]
  split_ifs <;> simp

end SlopeTestRemainingChoices

theorem gLCells : GLCells := by
  intro E _ _ _ _ n σ
  haveI : T2Space E := GroundTheory.Automorphic.GLnLocal.t2Space E
  obtain ⟨k, w, hcov, hanti⟩ :=
    GroundTheory.Automorphic.Parabolic.exists_cellEnumeration (F := E) (Fin.val : Fin n → ℕ) Fin.val
  have hcl := GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨k, fun j => permGL E (w j), fun j => sg_permGL σ _, fun g => ?_, fun j => ?_⟩
  · simpa only [doubleCoset_eq_cell] using hcov g
  · simpa only [doubleCoset_eq_cell] using hcl j

end UpperTheory.Gal.LocD

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.PrLeft
noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace UpperTheory.Gal.LocD

theorem prLeft : PrLeft := by
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ b
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨c', hc'⟩ : ∃ c' : NNReal, map (· * b) μ = c' • μ :=
    ⟨_, isMulLeftInvariant_eq_smul _ _⟩
  refine ⟨(((χ b)⁻¹ : ℂˣ) : ℂ) * ((c' : ℝ) : ℂ), fun f g => ?_⟩
  set H : B → ℂ := fun y => (χ y : ℂ) * f ((y : G)⁻¹ * g) with hH
  have key : pr B μ χ (fun x => f ((b : G)⁻¹ * x)) g
      = (((χ b)⁻¹ : ℂˣ) : ℂ) * ∫ x, H (x * b) ∂μ := by
    unfold pr
    rw [← integral_const_mul]
    congr 1
    ext x
    simp only [hH, map_mul, Units.val_mul, Subgroup.coe_mul, mul_inv_rev, mul_assoc]
    rw [Units.val_inv_eq_inv_val]
    field_simp [(χ b).ne_zero]
  have e := (MeasurableEquiv.mulRight b).measurableEmbedding.integral_map (μ := μ) H
  rw [MeasurableEquiv.coe_mulRight] at e
  rw [key, ← e, hc', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have : pr B μ χ f g = ∫ x, H x ∂μ := rfl
  rw [this]
  ring

end UpperTheory.Gal.LocD

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.EigZero
noncomputable section

namespace UpperTheory.Gal.LocD

private theorem common_eigenvector {T D : Type} [AddCommGroup D] [Module ℂ D] [FiniteDimensional ℂ D] [Nontrivial D]
    (φ : T → Module.End ℂ D) (hc : ∀ s t, Commute (φ s) (φ t)) :
    ∃ (l : D) (a : T → ℂ), l ≠ 0 ∧ ∀ t, φ t l = a t • l :=
  _root_.UpperTheory.Reformulated.B.CommonEigenvectorExistence.common_eigenvector φ hc

theorem eigZero : EigZero := by
  intro T J _ _ _ _ _ ρ
  have hcomm : ∀ s t, Commute (ρ s) (ρ t) := fun s t => by
    change ρ s * ρ t = ρ t * ρ s
    rw [← map_mul, ← map_mul, mul_comm]
  haveI : Nontrivial (Module.Dual ℂ J) := by
    obtain ⟨y, hy⟩ := exists_ne (0 : J)
    have hex : ∃ g : Module.Dual ℂ J, g y ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h)
    obtain ⟨g, hg⟩ := hex
    exact ⟨g, 0, fun h => hg (by simp [h])⟩
  obtain ⟨l, a, hl0, hl⟩ := common_eigenvector (fun t => (ρ t).dualMap) (fun s t => by
    change (ρ s).dualMap * (ρ t).dualMap = (ρ t).dualMap * (ρ s).dualMap
    ext g y
    have h := congrArg (fun F : Module.End ℂ J => F y) (hcomm s t).eq
    simp only [Module.End.mul_apply] at h
    simp [Module.End.mul_apply, LinearMap.dualMap_apply, h])
  have hact : ∀ t y, l (ρ t y) = a t * l y := fun t y => by
    have := congrArg (fun g : Module.Dual ℂ J => g y) (hl t)
    simpa [LinearMap.dualMap_apply] using this
  obtain ⟨y₀, hy₀⟩ : ∃ y, l y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hl0 (LinearMap.ext h)
  let am : T →* ℂ :=
    { toFun := a
      map_one' := by
        have := hact 1 y₀
        simp only [map_one, Module.End.one_apply] at this
        exact (mul_right_cancel₀ hy₀ (by rw [one_mul]; exact this)).symm
      map_mul' := fun s t => by
        have := hact (s * t) y₀
        rw [map_mul, Module.End.mul_apply, hact s, hact t, ← mul_assoc] at this
        exact (mul_right_cancel₀ hy₀ this).symm }
  refine ⟨am.toHomUnits, l, ?_, ?_, ?_⟩
  · exact hl0
  · intro t y
    simpa [am] using hact t y
  · have hval : ∀ t, ((am.toHomUnits t : ℂˣ) : ℂ) = a t := fun t => by simp [am]
    have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun t => ρ t) (fun s t _ => hcomm s t)
      (fun t => Module.End.iSup_maxGenEigenspace_eq_top (ρ t))
    obtain ⟨χ, y, hy, hly⟩ : ∃ (χ : T → ℂ) (y : J),
        y ∈ (⨅ t, Module.End.maxGenEigenspace (ρ t) (χ t) : Submodule ℂ J) ∧ l y ≠ 0 := by
      by_contra h
      push_neg at h
      have : (⊤ : Submodule ℂ J) ≤ LinearMap.ker l := by
        rw [← htop]
        exact iSup_le fun χ y hy => LinearMap.mem_ker.2 (h χ y hy)
      exact hl0 (LinearMap.ker_eq_top.1 (top_le_iff.1 this))
    have hpow : ∀ (t : T) (c : ℂ) (m : ℕ) (z : J), l (((ρ t - c • 1) ^ m) z) = (a t - c) ^ m * l z := by
      intro t c m
      induction m with
      | zero => intro z; simp
      | succ m ih =>
        intro z
        rw [pow_succ, Module.End.mul_apply, ih]
        simp [hact, pow_succ, sub_mul, mul_assoc]
    have hχ : ∀ t, χ t = a t := by
      intro t
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hy t)
      have h0 := hpow t (χ t) m y
      rw [hm, map_zero] at h0
      have : (a t - χ t) ^ m = 0 := by
        rcases mul_eq_zero.1 h0.symm with h | h
        · exact h
        · exact absurd h hly
      have hm0 : m ≠ 0 := by
        rintro rfl
        simp at this
      exact (sub_eq_zero.1 ((pow_eq_zero_iff hm0).1 this)).symm
    intro hbot
    have hy' : y ∈ (⨅ t, Module.End.maxGenEigenspace (ρ t) ((am.toHomUnits t : ℂˣ) : ℂ) : Submodule ℂ J) := by
      simp only [hval, ← hχ]
      exact hy
    rw [hbot, Submodule.mem_bot] at hy'
    exact hly (by rw [hy', map_zero])

end UpperTheory.Gal.LocD

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.EtaEx
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.etaEx :
    EtaEx := by
  intro G _ _ _ _ _ _ B s p hp hper P κ hκ hs hB hne
  obtain ⟨f₀, hf₀, g₀, h0⟩ := hne
  obtain ⟨K, hK, hKf⟩ := GroundTheory.Automorphic.exists_forall_mul_left (R := ℂ) hf₀
  set e : B → ℂ := fun b => P (fun x => f₀ ((b : G)⁻¹ * x)) g₀ / P f₀ g₀ with he
  have hη : ∀ (b : B) (f : G → ℂ) (g : G), P (fun x => f ((b : G)⁻¹ * x)) g = e b * P f g := by
    intro b f g
    obtain ⟨c, hc⟩ := hB b
    have hc0 := hc f₀ g₀
    have : e b = c := by
      rw [he]; dsimp only; rw [hc0, mul_div_assoc, div_self h0, mul_one]
    rw [this, hc]
  have hpow : ∀ (n : ℕ) (f : G → ℂ) (g : G), P (f ∘ s^[n]) g = (κ : ℂ) ^ n * P f (s^[n] g) := by
    intro n
    induction n with
    | zero => intro f g; simp
    | succ n ih =>
      intro f g
      rw [Function.iterate_succ, ← Function.comp_assoc, hs, ih, Function.comp_apply, pow_succ]
      ring
  have hper' : s^[p] = id := funext hper
  have hκ1 : κ = 1 := by
    have h1 := hpow p f₀ g₀
    rw [hper', Function.comp_id, id] at h1
    have hk : (κ : ℂ) ^ p = 1 := by
      have := mul_right_cancel₀ h0 (h1.symm.trans (one_mul _).symm)
      exact this
    have hk' : κ ^ p = 1 := by exact_mod_cast hk
    exact (pow_eq_one_iff_of_nonneg hκ.le hp.ne').1 hk'
  have e1 : e 1 = 1 := by
    rw [he]; dsimp only; simp [div_self h0]
  have emul : ∀ b b' : B, e (b * b') = e b * e b' := by
    intro b b'
    have h := hη b (fun x => f₀ ((b' : G)⁻¹ * x)) g₀
    rw [hη b' f₀ g₀] at h
    have h2 : e (b * b') * P f₀ g₀ = e b * e b' * P f₀ g₀ := by
      rw [← hη, mul_assoc, ← h]
      congr 1
      funext x
      simp [mul_assoc]
    exact mul_right_cancel₀ h0 h2
  let η : B →* ℂ := { toFun := e, map_one' := e1, map_mul' := emul }
  refine ⟨hκ1, η, fun b f g => hη b f g, ⟨K, K.isOpen, fun b hb => ?_⟩, fun b b' hbb => ?_⟩
  · show e b = 1
    rw [he]
    dsimp only
    have hfix : (fun x => f₀ ((b : G)⁻¹ * x)) = f₀ :=
      funext fun x => hKf _ (K.inv_mem (by exact hb)) x
    rw [hfix, div_self h0]
  · show e b' = e b
    have hg1 : s (s^[p - 1] g₀) = g₀ := by
      rw [← Function.iterate_succ_apply' (f := s), Nat.succ_eq_add_one, Nat.sub_add_cancel hp,
        hper]
    have hA := hη b (f₀ ∘ s) (s^[p - 1] g₀)
    rw [hs, hg1] at hA
    have hfun : (fun x => (f₀ ∘ s) ((b : G)⁻¹ * x)) = (fun x => f₀ ((b' : G)⁻¹ * x)) ∘ s := by
      funext x
      simp [hbb, map_mul, map_inv]
    rw [hfun, hs, hg1, hη b' f₀ g₀] at hA
    have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have h3 : e b' * P f₀ g₀ = e b * P f₀ g₀ := by
      have := mul_left_cancel₀ hκ0 (hA.trans (by ring : e b * (↑κ * P f₀ g₀) = ↑κ * (e b * P f₀ g₀)))
      exact this
    exact mul_right_cancel₀ h0 h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.PrAuto
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.prAuto :
    PrAuto := by
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ s p hp hs hper hsB hχ
  have hit : ∀ n (b : G), b ∈ B → s^[n] b ∈ B := by
    intro n
    induction n with
    | zero => intro b hb; simpa using hb
    | succ n ih =>
      intro b hb
      rw [Function.iterate_succ_apply']
      exact hsB _ (ih b hb)
  have hleft : ∀ g, s^[p - 1] (s g) = g := by
    intro g
    rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    exact hper g
  have hright : ∀ g, s (s^[p - 1] g) = g := by
    intro g
    rw [← Function.iterate_succ_apply' s, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    exact hper g
  let σ : B ≃ₜ* B :=
    { toFun := fun b => ⟨s b, hsB _ b.2⟩
      invFun := fun b => ⟨s^[p - 1] b, hit _ _ b.2⟩
      left_inv := fun b => Subtype.ext (hleft b)
      right_inv := fun b => Subtype.ext (hright b)
      map_mul' := fun a b => Subtype.ext (map_mul s (a : G) (b : G))
      continuous_toFun := (hs.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((hs.iterate _).comp continuous_subtype_val).subtype_mk _ }
  haveI : LocallyCompactSpace B := hB.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology B :=
    inferInstanceAs (SecondCountableTopology {x // x ∈ (B : Set G)})
  haveI hν : (Measure.map σ μ).IsHaarMeasure := σ.isHaarMeasure_map μ
  have heq := Measure.isMulLeftInvariant_eq_smul (Measure.map σ μ) μ
  refine ⟨Measure.haarScalarFactor (Measure.map σ μ) μ,
    Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, fun f g => ?_⟩
  have hint : ∀ b : B, (χ b : ℂ) * (f ∘ s) ((b : G)⁻¹ * g) =
      (χ (σ b) : ℂ) * f (((σ b : B) : G)⁻¹ * s g) := by
    intro b
    rw [hχ b (σ b) rfl]
    simp [σ, map_mul, map_inv]
  have hm : ∫ c, (χ c : ℂ) * f ((c : G)⁻¹ * s g) ∂(Measure.map σ μ) =
      ∫ b, (χ (σ b) : ℂ) * f (((σ b : B) : G)⁻¹ * s g) ∂μ :=
    integral_map_equiv σ.toHomeomorph.toMeasurableEquiv (fun c : B => (χ c : ℂ) * f ((c : G)⁻¹ * s g))
  unfold pr
  simp_rw [hint]
  rw [← hm]
  conv_lhs => rw [heq]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.PrSurj
noncomputable section

open MeasureTheory

namespace UpperTheory.Gal.LocD

theorem prSurj : PrSurj := by
  classical
  intro G _ _ _ _ _ _ B hB _ _ μ _ χ K hKo hKc hBK φ hφ
  obtain ⟨hφB, K0, hK0o, hφK0⟩ := mem_indF.1 hφ
  set S : Set B := {b | (b : G) ∈ K} with hS
  have hSo : IsOpen S := hKo.preimage continuous_subtype_val
  have hSc : IsCompact S := (hB.isClosedEmbedding_subtypeVal).isCompact_preimage hKc
  have hSpos : 0 < μ S := hSo.measure_pos μ ⟨1, K.one_mem⟩
  have hSfin : μ S < ⊤ := hSc.measure_lt_top
  have hr : (μ S).toReal ≠ 0 := (ENNReal.toReal_pos hSpos.ne' hSfin.ne).ne'
  have hr' : ((μ S).toReal : ℂ) ≠ 0 := by exact_mod_cast hr
  set c : ℂ := ((μ S).toReal : ℂ)⁻¹ with hc
  refine ⟨fun g => if g ∈ K then c * φ g else 0, ?_, ?_⟩
  · let K' : OpenSubgroup G := ⟨K ⊓ K0, hKo.inter hK0o⟩
    apply GroundTheory.Automorphic.mem_locallyConstantCompactSupport_of_forall_mul_right (R := ℂ) K'
    · exact HasCompactSupport.intro hKc (fun g hg => if_neg hg)
    · intro g k hk
      have hk' : k ∈ K ∧ k ∈ K0 := Subgroup.mem_inf.1 hk
      simp only [K.mul_mem_cancel_right hk'.1, hφK0 k hk'.2 g]
  · funext g
    obtain ⟨b0, hb0, k0, hk0, rfl⟩ := hBK g
    set b0' : B := ⟨b0, hb0⟩
    have key : ∀ b : B, ((b : G)⁻¹ * (b0 * k0) ∈ K) ↔ b ∈ (fun x => b0'⁻¹ * x) ⁻¹' S := by
      intro b
      simp only [Set.mem_preimage, hS, Set.mem_setOf_eq, Subgroup.coe_mul, Subgroup.coe_inv, b0']
      rw [← mul_assoc, K.mul_mem_cancel_right hk0, ← K.inv_mem_iff]
      simp [mul_inv_rev]
    have hTm : MeasurableSet ((fun x : B => b0'⁻¹ * x) ⁻¹' S) :=
      (hSo.preimage (continuous_const.mul continuous_id)).measurableSet
    have hint : (fun b : B => (χ b : ℂ) * (if ((b:G)⁻¹ * (b0 * k0)) ∈ K then c * φ ((b:G)⁻¹ * (b0*k0)) else 0))
        = ((fun x : B => b0'⁻¹ * x) ⁻¹' S).indicator (fun _ => c * φ (b0 * k0)) := by
      funext b
      by_cases h : ((b:G)⁻¹ * (b0 * k0)) ∈ K
      · rw [if_pos h, Set.indicator_of_mem ((key b).1 h)]
        have h1 := hφB b⁻¹ (b0 * k0)
        rw [Subgroup.coe_inv] at h1
        rw [h1]
        have hu : (χ b : ℂ) * (χ b⁻¹ : ℂ) = 1 := by
          rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
        linear_combination (c * φ (b0 * k0)) * hu
      · rw [if_neg h, Set.indicator_of_notMem (fun h' => h ((key b).2 h')), mul_zero]
    simp only [pr]
    rw [hint, integral_indicator_const _ hTm, measureReal_def, measure_preimage_mul]
    rw [hc, Complex.real_smul]
    field_simp

end UpperTheory.Gal.LocD

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.CellStep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD
open GroundTheory.Automorphic.Whittaker

theorem UpperTheory.Gal.LocD.cellStep :
    StabSub → CellStep := by
  intro hSt X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hsτ χ hχL D hD hsum U C x₀ hU hC hUC hHU hsU hsx₀ hvan f hf
  obtain ⟨L, hLo, hL1⟩ := hχL
  obtain ⟨L₀, hL₀c, hL₀o, hL₀L, hL₀τ⟩ := hSt H τ p hp hτ hτp L hLo
  have hχL₀ : ∀ l ∈ L₀, χ l = 1 := fun l hl => hL1 l (hL₀L hl)
  have hsp' : ∀ y, s^[p - 1 + 1] y = y := fun y => by rw [Nat.sub_add_cancel hp]; exact hsp y
  have toCc : ∀ g ∈ supportedIn U, g ∈ Cc X := by
    intro g hg
    obtain ⟨h1, -⟩ := hg
    exact h1
  let e : X ≃ₜ X :=
    { toFun := s
      invFun := s^[p - 1]
      left_inv := fun y => by
        show s^[p - 1] (s y) = y
        rw [← Function.iterate_succ_apply s (p - 1) y]
        exact hsp' y
      right_inv := fun y => by
        show s (s^[p - 1] y) = y
        rw [← Function.iterate_succ_apply' s (p - 1) y]
        exact hsp' y
      continuous_toFun := hs
      continuous_invFun := hs.iterate (p - 1) }
  have hcomp : ∀ g ∈ supportedIn U, g ∘ s ∈ supportedIn U := by
    intro g hg
    obtain ⟨hg1, hsupp⟩ := hg
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hg1
    obtain ⟨hlc, hcs⟩ := hg1
    refine ⟨GroundTheory.Automorphic.mem_locallyConstantCompactSupport.2
      ⟨hlc.comp_continuous hs, hcs.comp_homeomorph e⟩, ?_⟩
    intro x hx
    exact (hsU x).1 (hsupp hx)
  have hiter : ∀ i, ∀ g ∈ supportedIn U, g ∘ s^[i] ∈ supportedIn U := by
    intro i
    induction i with
    | zero =>
      intro g hg
      exact hg
    | succ i ih =>
      intro g hg
      exact hcomp _ (ih g hg)
  obtain ⟨f₀, hf₀U, hf₀eq⟩ :=
    exists_lift_orbit_piece hU hC hUC hL₀c hL₀o (y := x₀) (mem_orbit_self x₀)
  have hs_orb : ∀ y ∈ orbit H x₀, s y ∈ orbit H x₀ := by
    rintro _ ⟨h, rfl⟩
    exact ⟨τ h, by
      show τ h • x₀ = s (h • x₀)
      rw [hsτ, hsx₀]⟩
  have hs_piece : ∀ z ∈ orbitPiece L₀ x₀, s z ∈ orbitPiece L₀ x₀ := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨τ l, (hL₀τ l).2 hl, by
      show τ l • x₀ = s (l • x₀)
      rw [hsτ, hsx₀]⟩
  have hpiece_iter : ∀ n, ∀ z ∈ orbitPiece L₀ x₀, s^[n] z ∈ orbitPiece L₀ x₀ := by
    intro n
    induction n with
    | zero =>
      intro z hz
      exact hz
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      exact hs_piece _ (ih z hz)
  have hs_piece_iff : ∀ z, s z ∈ orbitPiece L₀ x₀ ↔ z ∈ orbitPiece L₀ x₀ := by
    intro z
    refine ⟨fun hz => ?_, hs_piece z⟩
    have h1 := hpiece_iter (p - 1) _ hz
    rw [← Function.iterate_succ_apply s (p - 1) z, hsp'] at h1
    exact h1
  have hf₀s : ∀ x ∈ orbit H x₀, f₀ (s x) = f₀ x := by
    intro x hx
    rw [hf₀eq _ (hs_orb x hx), hf₀eq x hx]
    by_cases hz : x ∈ orbitPiece L₀ x₀
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hs_piece_iff x).2 hz)]
      rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((hs_piece_iff x).1 h))]
  have hf₀i : ∀ i, ∀ x ∈ orbit H x₀, f₀ (s^[i] x) = f₀ x := by
    intro i
    induction i with
    | zero =>
      intro x _
      rfl
    | succ i ih =>
      intro x hx
      rw [Function.iterate_succ_apply, ih _ (hs_orb x hx)]
      exact hf₀s x hx
  have hDi : ∀ i, D (f₀ ∘ s^[i]) = D f₀ := by
    intro i
    have hm := sub_mem_of_eqOn_orbit hUC (hiter i f₀ hf₀U) hf₀U (fun x hx => hf₀i i x hx)
    have h0 := hvan _ hm
    rwa [map_sub, sub_eq_zero] at h0
  have hD0 : D f₀ = 0 := by
    have h0 := hsum f₀ (toCc f₀ hf₀U)
    simp only [hDi, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr hp.ne')
    · exact h
  let W : Submodule ℂ (X → ℂ) := supportedIn U ⊓ LinearMap.ker D
  have hrel : relSpan χ U ≤ W := by
    refine le_inf (relSpan_le_supportedIn χ hHU) (Submodule.span_le.mpr ?_)
    rintro g ⟨h, f', hf'U, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul]
    rw [hD h f' (toCc f' hf'U)]
    ring
  have hmem : f₀ ∈ W ⊔ supportedIn U ⊓ vanishingOn C :=
    Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hf₀U, LinearMap.mem_ker.mpr hD0⟩)
  have hle := supportedIn_le_of_base hU hC hUC hHU χ (W := W) inf_le_left hrel L₀ hL₀c hL₀o
    hχL₀ f₀ hf₀eq hmem
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hle hf)
  rw [map_add (f := _), LinearMap.mem_ker.mp (Submodule.mem_inf.mp ha).2, hvan b hb, add_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.JacSemi
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

namespace UpperTheory.Gal.LocD

private theorem sg_diagT {E : Type} [Field E] {n : ℕ} (σ : E ≃+* E) (t : Fin n → Eˣ) :
    sg σ (diagT E (Fin n) t) = diagT E (Fin n) (fun i => Units.map (σ : E →* E) (t i)) := by
  ext i j
  rw [sg_val, val_diagT, val_diagT]
  by_cases h : i = j
  · subst h
    simp
  · simp [diagonal_apply_ne _ h]

private theorem absPow_map {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {σ : E ≃+* E} (hσ : Isom σ) (s : ℂ) (x : Eˣ) :
    absPow E s (Units.map (σ : E →* E) x) = absPow E s x := by
  have hx : ((Units.map (σ : E →* E) x : Eˣ) : E) = σ x := rfl
  have h1 : valuation E ((Units.map (σ : E →* E) x * x⁻¹ : Eˣ) : E) = 1 := by
    rw [Units.val_mul, hx, map_mul, hσ, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀]
    exact (Valuation.ne_zero_iff _).2 x.ne_zero
  have h2 := isUnram_absPow E s _ h1
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  exact h2

private theorem deltaHalf_map {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] {n : ℕ} {σ : E ≃+* E} (hσ : Isom σ) (t : Fin n → Eˣ) :
    deltaHalf E (fun _ : Fin n => Unit) (leviTorus E (Fin n) (fun i => Units.map (σ : E →* E) (t i))) =
      deltaHalf E (fun _ : Fin n => Unit) (leviTorus E (Fin n) t) := by
  have hdet : ∀ (u : Fin n → Eˣ) (a : Fin n),
      GeneralLinearGroup.det ((leviTorus E (Fin n) u) a) = u a :=
    fun u a => congrFun ((leviTorus E (Fin n)).symm_apply_apply u) a
  rw [deltaHalf_apply, deltaHalf_apply]
  simp only [hdet]
  exact Finset.prod_congr rfl (fun a _ => absPow_map hσ _ _)

end UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.jacSemi :
    JacSemi := by
  intro E _ _ _ _ n σ hσ V _ _ π A hA t y
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hj : ∀ (s : Fin n → Eˣ) (w : V), jacB π s (Submodule.Quotient.mk w) =
      (((deltaHalf E (fun _ : Fin n => Unit) (leviTorus E (Fin n) s))⁻¹ : ℂˣ) : ℂ) •
        (Submodule.Quotient.mk (π (diagT E (Fin n) s) w) : Jacquet π (unipB E (Fin n))) := fun _ _ => rfl
  rw [hj, map_smul, jacA_mk, jacA_mk, hj, hA, sg_diagT, deltaHalf_map hσ]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.DistInv
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

private theorem comp_mem_Cc {X : Type} [TopologicalSpace X] (s : X → X) (q : ℕ) (hs : Continuous s)
    (hsp : ∀ x, s^[q + 1] x = x) {f : X → ℂ} (hf : f ∈ Cc X) : f ∘ s ∈ Cc X := by
  obtain ⟨h1, h2⟩ := hf
  let e : X ≃ₜ X :=
    { toFun := s
      invFun := s^[q]
      left_inv := fun y => by
        show s^[q] (s y) = y
        rw [← Function.iterate_succ_apply s q y, hsp]
      right_inv := fun y => by
        show s (s^[q] y) = y
        rw [← Function.iterate_succ_apply' s q y, hsp]
      continuous_toFun := hs
      continuous_invFun := hs.iterate q }
  exact ⟨h1.comp_continuous hs, h2.comp_homeomorph e⟩

theorem UpperTheory.Gal.LocD.distInv :
    DistZero → DistInv := by
  intro hZ X H _ _ _ _ _ _ _ _ _ _ _ _ _ s τ p hp hs hτ hsp hτp hsτ χ hχL hχτ k x hxs horb hcl D hD f hf
  have hsp' : ∀ y, s^[p - 1 + 1] y = y := fun y => by rw [Nat.sub_add_cancel hp]; exact hsp y
  have cc : ∀ g ∈ Cc X, g ∘ s ∈ Cc X := fun g hg => comp_mem_Cc s (p - 1) hs hsp' hg
  let D' : (X → ℂ) →ₗ[ℂ] ℂ := D.comp (LinearMap.funLeft ℂ ℂ s) - D
  have hD'apply : ∀ g, D' g = D (g ∘ s) - D g := fun g => rfl
  have key := hZ X H s τ p hp hs hτ hsp hτp hsτ χ hχL k x hxs horb hcl D' ?_ ?_ f hf
  · rw [hD'apply, sub_eq_zero] at key
    exact key
  · intro h g hg
    rw [hD'apply, hD'apply]
    set h' := τ^[p - 1] h with hh'
    have hτh : τ h' = h := by
      rw [hh', ← Function.iterate_succ_apply' τ (p - 1) h, Nat.succ_eq_add_one,
        Nat.sub_add_cancel hp, hτp]
    have hχh : χ h' = χ h := by rw [← hχτ h', hτh]
    have hcomp : GroundTheory.Automorphic.Whittaker.transl h g ∘ s
        = GroundTheory.Automorphic.Whittaker.transl h' (g ∘ s) := by
      ext y
      simp only [Function.comp_apply, GroundTheory.Automorphic.Whittaker.transl_apply]
      rw [hsτ, map_inv, hτh]
    rw [hcomp, hD h' _ (cc g hg), hD h g hg, hχh]
    ring
  · intro g hg
    have h1 : ∀ i, D' (g ∘ s^[i]) = D (g ∘ s^[i + 1]) - D (g ∘ s^[i]) := fun i => rfl
    simp only [h1]
    rw [Finset.sum_range_sub (fun i => D (g ∘ s^[i]))]
    have hid : s^[p] = id := funext hsp
    simp [hid]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.PrMem
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix MeasureTheory UpperTheory.ConvolutionTheory.Loc MulAction UpperTheory.Gal.LocD

theorem UpperTheory.Gal.LocD.prMem :
    PrMem := by
  intro G _ _ _ _ _ _ _ B hB _ _ μ _ χ hker
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology _
  have hχc : Continuous (fun x : B => (χ x : ℂ)) := by
    have := continuous_of_continuousAt_one ((Units.coeHom ℂ).comp χ) ?_
    · exact this
    · refine (continuousAt_const (y := (1 : ℂ))).congr ?_
      filter_upwards [hker.mem_nhds (one_mem χ.ker)] with x hx
      have hx' : χ x = 1 := MonoidHom.mem_ker.mp hx
      simp [hx']
  have hint : ∀ f ∈ Cc G, ∀ g : G,
      Integrable (fun x : B => (χ x : ℂ) * f ((x : G)⁻¹ * g)) μ := by
    intro f hf g
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf
    obtain ⟨hlc, hcs⟩ := hf
    have hemb : Topology.IsClosedEmbedding (fun x : B => (x : G)⁻¹ * g) :=
      ((Homeomorph.inv G).trans (Homeomorph.mulRight g)).isClosedEmbedding.comp
        hB.isClosedEmbedding_subtypeVal
    have hcs' : HasCompactSupport (fun x : B => f ((x : G)⁻¹ * g)) :=
      hcs.comp_isClosedEmbedding hemb
    exact Continuous.integrable_of_hasCompactSupport
      (hχc.mul (hlc.continuous.comp hemb.continuous)) hcs'.mul_left
  refine ⟨fun f hf => ?_, fun f hf f' hf' => ?_⟩
  · rw [mem_indF]
    constructor
    · intro b g
      simp only [pr]
      rw [← integral_mul_left_eq_self _ b, ← integral_const_mul]
      congr 1
      ext x
      simp only [map_mul, Units.val_mul, Subgroup.coe_mul, _root_.mul_inv_rev, mul_assoc,
        inv_mul_cancel_left]
    · obtain ⟨K, -, hK⟩ := GroundTheory.Automorphic.exists_forall_mul_right hf
      refine ⟨(K : Subgroup G), K.isOpen, fun k hk g => ?_⟩
      simp only [pr]
      congr 1
      ext x
      rw [← mul_assoc, hK _ _ hk]
  · funext g
    simp only [pr, Pi.add_apply, mul_add]
    exact integral_add (hint f hf g) (hint f' hf' g)
end

namespace UpperTheory.Gal.LocD

theorem funInv_holds : FunInv := by
  have dist := distInv (distZero (cellStep stabSub))
  exact funInv (biInv dist) prMem prLeft prAuto prSurj etaEx

theorem scalar_holds : Scalar := by
  have fi := funInv_holds
  exact scalar_of (eig eigZero) toBorel jacSemi (core fi gLCells gLFacts)

theorem locDesc_holds : LocDesc := locDesc_of scalar_holds tracePow

theorem ofSupport_holds : OfSupport := ofSupport

end UpperTheory.Gal.LocD
