module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberZeroSmallImage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharacters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestFamiliesProjectedTranslationOperators

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorTraceEqConstMulLocalTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_admissible_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N), π.IsIrreducible → IsAdmissible π → ∀ φ : N →ₗ[ℂ] N, (∀ g x, φ (π g x) = π g (φ x)) → ∃ c : ℂ, φ = c • LinearMap.id := by
  first | exact @GlobalTheory.SchurAdm.schur_admissible | exact GlobalTheory.SchurAdm.schur_admissible | (intros; apply GlobalTheory.SchurAdm.schur_admissible <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMulEndomorphismIsotypicRep
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerMemISupRangeEqSumSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerMemISupRangeEqSumSmul
namespace GlobalTheory

open Representation

theorem intertwiner_mem_iSup_range_eq_sum_smul (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hS : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id)
    (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ)
    (hinj : Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)))
    (ψ : π.IntertwiningMap ρ)
    (hψ : LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap) :
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by
  classical
  let Φ : (Fin m → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
  have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by
    intro w; simp [Φ, LinearMap.sum_apply]
  have hΦinj : Function.Injective Φ := by
    intro a b h; apply hinj; simpa [hΦ] using h
  have hle : (⨆ j, LinearMap.range (φ j).toLinearMap) ≤ LinearMap.range Φ := by
    refine iSup_le fun j => ?_
    rintro _ ⟨n, rfl⟩
    refine ⟨Pi.single j n, ?_⟩
    rw [hΦ]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  have hmem : ∀ n, ψ.toLinearMap n ∈ LinearMap.range Φ := fun n =>
    hle (hψ ⟨n, rfl⟩)
  let e := LinearEquiv.ofInjective Φ hΦinj
  let Wm : N →ₗ[ℂ] (Fin m → N) := e.symm.toLinearMap ∘ₗ ψ.toLinearMap.codRestrict _ hmem
  have hW : ∀ n, Φ (Wm n) = ψ n := by
    intro n
    simp only [Wm, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 : e (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ⟨ψ.toLinearMap n, hmem n⟩ := e.apply_symm_apply _
    have h3 := congrArg Subtype.val h2
    change Φ (e.symm ⟨ψ.toLinearMap n, hmem n⟩) = ψ n
    rw [← LinearEquiv.ofInjective_apply Φ (h := hΦinj)]
    exact h3
  have hWg : ∀ g n, Wm (π g n) = fun j => π g (Wm n j) := by
    intro g n
    apply hΦinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hW, hΦ, ψ.isIntertwining, ← hW, hΦ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(φ j).isIntertwining]
  have hc : ∀ j, ∃ c : ℂ, ∀ n, Wm n j = c • n := by
    intro j
    let θ : π.IntertwiningMap π :=
      (LinearMap.proj j ∘ₗ Wm).intertwiningMap_of_isIntertwiningMap π π (by
        intro g v
        simp [hWg])
    obtain ⟨c, hc⟩ := hS θ
    refine ⟨c, fun n => ?_⟩
    have h1 : Wm n j = θ.toLinearMap n := rfl
    rw [h1, hc]
    simp
  choose c hc using hc
  refine ⟨c, fun n => ?_⟩
  rw [← hW, hΦ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, map_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerMemISupRangeEqSumSmulStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X),
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) →
    ∀ ψ : π.IntertwiningMap ρ, LinearMap.range ψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap →
    ∃ c : Fin m → ℂ, ∀ n, ψ n = ∑ j, c j • φ j n := by
  first | exact @GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul | exact GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul | (intros; apply GlobalTheory.intertwiner_mem_iSup_range_eq_sum_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveSumOfLinIndepIntertwiners
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveSumOfLinIndepIntertwiners
namespace GlobalTheory

open Representation

theorem intertwiner_sum_eq_zero_imp {G : Type} [Group G] {N X : Type} [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hirr : π.IsIrreducible)
    (hschur : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) :
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
      ∀ w : Fin m → N, ∑ j, φ j (w j) = 0 → w = 0 := by
  intro m
  induction m with
  | zero => intro φ _ w _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro φ hφ
    let Φ : (Fin (m+1) → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
    have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by intro w; simp [Φ, LinearMap.sum_apply]
    let K := LinearMap.ker Φ
    have hK : ∀ w, w ∈ K ↔ ∑ j, φ j (w j) = 0 := by intro w; simp [K, hΦ]
    have hφ' : LinearIndependent ℂ (fun j : Fin m => φ j.castSucc) :=
      hφ.comp _ (Fin.castSucc_injective m)
    have claimA : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) = 0 → w = 0 := by
      intro w hw hl
      rw [Fin.sum_univ_castSucc, hl, map_zero, add_zero] at hw
      have := ih _ hφ' (fun j => w j.castSucc) hw
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hl
      · exact congrFun this j
    have hstable : ∀ (g : G) (w : Fin (m+1) → N), ∑ j, φ j (w j) = 0 →
        ∑ j, φ j (π g (w j)) = 0 := by
      intro g w hw
      simp_rw [IntertwiningMap.isIntertwining]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hw, map_zero]
    let P : Subrepresentation π :=
      { toSubmodule := K.map (LinearMap.proj (Fin.last m))
        apply_mem_toSubmodule := by
          rintro g _ ⟨w, hw, rfl⟩
          refine ⟨fun j => π g (w j), ?_, rfl⟩
          rw [SetLike.mem_coe, hK] at hw ⊢
          exact hstable g w hw }
    have hmemP : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) ∈ P := fun w hw =>
      show w (Fin.last m) ∈ K.map (LinearMap.proj (Fin.last m)) from ⟨w, (hK w).2 hw, rfl⟩
    rcases hirr.eq_bot_or_eq_top P with hP | hP
    · intro w hw
      apply claimA w hw
      have := hmemP w hw
      rw [hP] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exfalso
      have hsurj : ∀ n : N, ∃ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 ∧ w (Fin.last m) = n := by
        intro n
        have : n ∈ P := by rw [hP]; exact Submodule.mem_top
        obtain ⟨w, hw, rfl⟩ := (show n ∈ K.map (LinearMap.proj (Fin.last m)) from this)
        exact ⟨w, (hK w).1 hw, rfl⟩
      have huniq : ∀ w w' : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → ∑ j, φ j (w' j) = 0 →
          w (Fin.last m) = w' (Fin.last m) → w = w' := by
        intro w w' hw hw' hl
        have := claimA (w - w') (by simp [map_sub, Finset.sum_sub_distrib, hw, hw'])
          (by simp [hl])
        exact sub_eq_zero.mp this
      let p : K →ₗ[ℂ] N := LinearMap.proj (Fin.last m) ∘ₗ K.subtype
      have hp : Function.Bijective p := by
        constructor
        · intro a b hab
          exact Subtype.ext (huniq a.1 b.1 ((hK _).1 a.2) ((hK _).1 b.2) hab)
        · intro n
          obtain ⟨w, hw, hl⟩ := hsurj n
          exact ⟨⟨w, (hK w).2 hw⟩, hl⟩
      let e := LinearEquiv.ofBijective p hp
      let s : N →ₗ[ℂ] (Fin (m+1) → N) := K.subtype ∘ₗ e.symm.toLinearMap
      have hsK : ∀ n, ∑ j, φ j (s n j) = 0 := fun n => (hK _).1 (e.symm n).2
      have hsl : ∀ n, s n (Fin.last m) = n := fun n => e.apply_symm_apply n
      have hsg : ∀ (g : G) (n : N), s (π g n) = fun j => π g (s n j) := by
        intro g n
        apply huniq _ _ (hsK _) (hstable g _ (hsK n))
        simp only [hsl]
      have hc : ∀ j : Fin m, ∃ c : ℂ, ∀ n, s n j.castSucc = c • n := by
        intro j
        let f : π.IntertwiningMap π :=
          { toLinearMap := LinearMap.proj j.castSucc ∘ₗ s
            isIntertwining' := by
              intro g; ext n; simp [hsg] }
        obtain ⟨c, hc⟩ := hschur f
        refine ⟨c, fun n => ?_⟩
        have := congrArg (fun L => L n) hc
        simpa [f] using this
      choose c hc using hc
      have hrel : ∑ j : Fin m, c j • φ j.castSucc + φ (Fin.last m) = 0 := by
        ext n
        have := hsK n
        rw [Fin.sum_univ_castSucc] at this
        simp only [hc, hsl, map_smul] at this
        simpa [IntertwiningMap.sum_apply] using this
      have := (Fintype.linearIndependent_iff.mp hφ) (Fin.snoc c 1) (by
        rw [Fin.sum_univ_castSucc]; simpa using hrel)
      have h1 := this (Fin.last m)
      simp at h1

theorem intertwiners_indep_injective : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by
  intro G _ N X _ _ _ _ π ρ hirr hschur m φ hφ a b hab
  have := intertwiner_sum_eq_zero_imp π ρ hirr hschur m φ hφ (a - b)
    (by simpa [map_sub, Finset.sum_sub_distrib, sub_eq_zero] using hab)
  exact sub_eq_zero.mp this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveSumOfLinIndepIntertwinersStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_sum_of_linIndep_intertwiners : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by
  first | exact @GlobalTheory.intertwiners_indep_injective | exact GlobalTheory.intertwiners_indep_injective | (intros; apply GlobalTheory.intertwiners_indep_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMatrixPiOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMatrixPiOperator
namespace GlobalTheory

theorem trace_matrix_pi_operator : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ)
    (h : Matrix (Fin m) (Fin m) ℂ) (A : W →ₗ[ℂ] W),
    LinearMap.trace ℂ (Fin m → W) (∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ
      LinearMap.proj j)) = h.trace * LinearMap.trace ℂ W A := by
  intro W _ _ _ m h A
  have key : ∀ k j : Fin m, LinearMap.trace ℂ (Fin m → W)
      (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ LinearMap.proj j)
      = if k = j then LinearMap.trace ℂ W A else 0 := by
    intro k j
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    by_cases hkj : k = j
    · subst hkj
      rw [LinearMap.proj_comp_single_same, LinearMap.comp_id, if_pos rfl]
    · rw [LinearMap.proj_comp_single_ne (R := ℂ) (φ := fun _ : Fin m => W) j k (Ne.symm hkj), LinearMap.comp_zero, map_zero, if_neg hkj]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.sum_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMatrixPiOperatorStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_sum_single_comp_proj_eq : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ)
    (h : Matrix (Fin m) (Fin m) ℂ) (A : W →ₗ[ℂ] W),
    LinearMap.trace ℂ (Fin m → W) (∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ : Fin m => W) k ∘ₗ A ∘ₗ
      LinearMap.proj j)) = h.trace * LinearMap.trace ℂ W A := by
  first | exact @GlobalTheory.trace_matrix_pi_operator | exact GlobalTheory.trace_matrix_pi_operator | (intros; apply GlobalTheory.trace_matrix_pi_operator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMulEndomorphismIsotypicRep
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.IsoTrace

theorem intertwining_sum_apply {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
    {π : Representation ℂ G N} {ρ : Representation ℂ G X} {ι : Type} (t : Finset ι)
    (c : ι → ℂ) (φ : ι → π.IntertwiningMap ρ) (n : N) : (∑ j ∈ t, c j • φ j) n = ∑ j ∈ t, c j • φ j n := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => simp [Finset.sum_insert ha, ih]

theorem trace_mul_isotypic : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible → (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) → IsIsotypicAlg π ρ → ∀ H : X →ₗ[ℂ] X, (∀ g x, H (ρ g x) = ρ g (H x)) → (∃ s : Finset (π.IntertwiningMap ρ), LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) → ∃ c : ℂ, ∀ (A : N →ₗ[ℂ] N) (B : X →ₗ[ℂ] X), (∀ φ : π.IntertwiningMap ρ, B ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ A) → ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (H ∘ₗ B) (c * b) := by
  intro G _ N X _ _ _ _ π ρ hirr hschur hiso H hH ⟨s, hs⟩
  let S := Submodule.span ℂ (s : Set (π.IntertwiningMap ρ))
  haveI : FiniteDimensional ℂ S := FiniteDimensional.span_finset ℂ s
  let bS := Module.finBasis ℂ S
  let φ : Fin (Module.finrank ℂ S) → π.IntertwiningMap ρ := fun j => (bS j : π.IntertwiningMap ρ)
  have hli : LinearIndependent ℂ φ := bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hinj := GlobalTheory.T.injective_sum_of_linIndep_intertwiners G N X π ρ hirr hschur _ φ hli
  have hY : LinearMap.range H ≤ ⨆ j, LinearMap.range (φ j).toLinearMap := by
    refine hs.trans (iSup₂_le fun ψ hψ => ?_)
    have hψS : ψ ∈ S := Submodule.subset_span hψ
    have e : ψ = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j := by
      have := congrArg Subtype.val (bS.sum_repr ⟨ψ, hψS⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    rintro _ ⟨n, rfl⟩
    have hn : ψ n = ∑ j, bS.repr ⟨ψ, hψS⟩ j • φ j n := by
      rw [← intertwining_sum_apply, ← e]
    change ψ n ∈ _
    rw [hn]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem j ⟨n, rfl⟩)
  have hcoef : ∀ ψ : π.IntertwiningMap ρ, ∃ c : Fin (Module.finrank ℂ S) → ℂ,
      ∀ n, H (ψ n) = ∑ j, c j • φ j n := by
    intro ψ
    let Hψ : π.IntertwiningMap ρ := (H ∘ₗ ψ.toLinearMap).intertwiningMap_of_isIntertwiningMap π ρ
      (fun g v => by simp [ψ.isIntertwining, hH])
    have hr : LinearMap.range Hψ.toLinearMap ≤ ⨆ j, LinearMap.range (φ j).toLinearMap := by
      rintro _ ⟨n, rfl⟩
      exact hY ⟨ψ n, rfl⟩
    exact GlobalTheory.T.exists_eq_sum_smul_of_range_le_iSup_range G N X π ρ hschur _ φ hinj Hψ hr
  choose hc hhc using fun j => hcoef (φ j)
  refine ⟨∑ j, hc j j, fun A B hB b hb => ?_⟩
  obtain ⟨hfin, htr⟩ := hb
  let R := LinearMap.range A
  let Φ' : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] X :=
    ∑ j, (φ j).toLinearMap ∘ₗ R.subtype ∘ₗ LinearMap.proj j
  have hΦ' : ∀ w, Φ' w = ∑ j, φ j (w j : N) := by
    intro w
    simp [Φ', LinearMap.sum_apply]
  have hinj' : Function.Injective Φ' := by
    intro w w' e
    rw [hΦ', hΦ'] at e
    have := hinj e
    funext j
    exact Subtype.ext (congrFun this j)
  let Z := LinearMap.range Φ'
  have hBφ : ∀ (ψ : π.IntertwiningMap ρ) n, B (ψ n) = ψ (A n) := fun ψ n =>
    DFunLike.congr_fun (hB ψ) n
  have hrange : LinearMap.range (H ∘ₗ B) ≤ Z := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ ⨆ f : π.IntertwiningMap ρ, LinearMap.range f.toLinearMap := by
      have : x ∈ isoPartAlg π ρ := hiso ▸ Submodule.mem_top
      exact this
    refine Submodule.iSup_induction _ (motive := fun x => (H ∘ₗ B) x ∈ Z) hx ?_ ?_ ?_
    · rintro ψ _ ⟨n, rfl⟩
      obtain ⟨c, hc'⟩ := hcoef ψ
      refine ⟨fun j => c j • ⟨A n, LinearMap.mem_range_self A n⟩, ?_⟩
      rw [hΦ']
      simp only [LinearMap.comp_apply, Pi.smul_apply, SetLike.val_smul, map_smul]
      rw [show ψ.toLinearMap n = ψ n from rfl, hBφ, hc']
    · simp
    · intro x y hx hy
      simpa using Z.add_mem hx hy
  haveI : FiniteDimensional ℂ Z := LinearMap.finiteDimensional_range Φ'
  have hT1 := GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional X (H ∘ₗ B) Z hrange
  let e : (Fin (Module.finrank ℂ S) → R) ≃ₗ[ℂ] Z := LinearEquiv.ofInjective Φ' hinj'
  let A' : R →ₗ[ℂ] R := A.restrict (p := R) (q := R) fun v _ => LinearMap.mem_range_self A v
  let h : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ := Matrix.of fun k j => hc j k
  let M : (Fin (Module.finrank ℂ S) → R) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → R) :=
    ∑ k, ∑ j, h k j • (LinearMap.single ℂ (fun _ => R) k ∘ₗ A' ∘ₗ LinearMap.proj j)
  have hM : ∀ w k, (M w k : N) = ∑ j, hc j k • A (w j) := by
    intro w k
    simp [M, h, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply, A']
  have hconj : (H ∘ₗ B).restrict (p := Z) (q := Z) (fun x _ => hrange (LinearMap.mem_range_self _ x)) =
      e.conj M := by
    refine LinearMap.ext fun z => Subtype.ext ?_
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    change H (B (Φ' w)) = Φ' (M w)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦ', hΦ', map_sum, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [hBφ, hhc, hM, map_sum, map_smul]
    rw [Finset.sum_comm]
  have key : LinearMap.trace ℂ Z ((H ∘ₗ B).restrict (p := Z) (q := Z)
      fun x _ => hrange (LinearMap.mem_range_self _ x)) = (∑ j, hc j j) * b := by
    rw [hconj, LinearMap.trace_conj', GlobalTheory.T.trace_sum_single_comp_proj_eq R _ h A', ← htr]
    simp [h, Matrix.trace, A', R]
  rw [← key]
  exact hT1

end GlobalTheory.IsoTrace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceMulEndomorphismIsotypicRepStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_mul_endomorphism_isotypicRep : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible → (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) → IsIsotypicAlg π ρ → ∀ H : X →ₗ[ℂ] X, (∀ g x, H (ρ g x) = ρ g (H x)) → (∃ s : Finset (π.IntertwiningMap ρ), LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) → ∃ c : ℂ, ∀ (A : N →ₗ[ℂ] N) (B : X →ₗ[ℂ] X), (∀ φ : π.IntertwiningMap ρ, B ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ A) → ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (H ∘ₗ B) (c * b) := by
  first | exact @GlobalTheory.IsoTrace.trace_mul_isotypic | exact GlobalTheory.IsoTrace.trace_mul_isotypic | (intros; apply GlobalTheory.IsoTrace.trace_mul_isotypic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetLocalComponentCopiesFixedAway
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetLocalComponentCopiesFixedAway
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.FinMultAway

section Abstract

variable {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
  {π : Representation ℂ G N} {ρ : Representation ℂ G X}

theorem apply_comm (φ : π.IntertwiningMap ρ) (g : G) (n : N) : φ.toLinearMap (π g n) = ρ g (φ.toLinearMap n) :=
  LinearMap.congr_fun (φ.isIntertwining' g) n

theorem isSemisimple_of_isotypic (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) : ρ.IsSemisimpleRepresentation := by
  haveI := hπ
  have hs : π.IsSemisimpleRepresentation :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule π).2 inferInstance
  exact GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range G X ρ (π.IntertwiningMap ρ) (fun _ => N) (fun _ => π)
    (fun φ => φ.toLinearMap) (fun _ => hs) (fun φ g x => apply_comm φ g x) h

theorem stable_biSup (s : Finset (π.IntertwiningMap ρ)) (g : G) :
    ∀ x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap, ρ g x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  intro x hx
  have : (⨆ φ ∈ s, LinearMap.range φ.toLinearMap) ≤ (⨆ φ ∈ s, LinearMap.range φ.toLinearMap).comap (ρ g) := by
    refine iSup₂_le fun φ hφ => ?_
    rintro _ ⟨n, rfl⟩
    rw [Submodule.mem_comap, ← apply_comm]
    exact Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ ⟨_, rfl⟩)
  exact this hx

theorem exists_intertwining_le (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) (C : Subrepresentation ρ)
    (hC : C ≠ ⊥) : ∃ ψ : π.IntertwiningMap ρ, Function.Injective ψ ∧ ∀ n, ψ n ∈ C.toSubmodule := by
  haveI := hπ
  haveI := isSemisimple_of_isotypic hπ h
  obtain ⟨C1, hc⟩ := exists_isCompl C
  have hc' : IsCompl C.toSubmodule C1.toSubmodule :=
    IsCompl.of_eq (congrArg Subrepresentation.toSubmodule hc.inf_eq_bot)
      (congrArg Subrepresentation.toSubmodule hc.sup_eq_top)
  let P : X →ₗ[ℂ] X := C.toSubmodule.subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ hc'
  have hPl : ∀ a ∈ C.toSubmodule, P a = a := fun a ha =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc' ⟨a, ha⟩)
  have hPr : ∀ b ∈ C1.toSubmodule, P b = 0 := fun b hb =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc' ⟨b, hb⟩)
  have hPi : ∀ g x, P (ρ g x) = ρ g (P x) := fun g x => by
    have hx : x ∈ C.toSubmodule ⊔ C1.toSubmodule := by rw [hc'.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hPl a ha, hPr b hb, hPl _ (C.apply_mem_toSubmodule g ha),
      hPr _ (C1.apply_mem_toSubmodule g hb), add_zero, add_zero]
  have hPm : ∀ x, P x ∈ C.toSubmodule := fun x => by simp [P]
  obtain ⟨c, hc0, hcne⟩ : ∃ c ∈ C.toSubmodule, c ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hC (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun x hx => hn x hx))
  by_contra hno
  push_neg at hno
  have hall : ∀ φ : π.IntertwiningMap ρ, LinearMap.range φ.toLinearMap ≤ LinearMap.ker P := by
    intro φ
    let ψ : π.IntertwiningMap ρ := ⟨P ∘ₗ φ.toLinearMap, fun g => LinearMap.ext fun n => by
      simp only [LinearMap.comp_apply]
      rw [apply_comm φ g n, hPi]⟩
    rcases Representation.IsIrreducible.injective_or_eq_zero ψ with hi | h0
    · obtain ⟨n, hn⟩ := hno ψ hi
      exact absurd (hPm _) hn
    · rintro _ ⟨n, rfl⟩
      exact DFunLike.congr_fun h0 n
  have : c ∈ LinearMap.ker P := by
    have h1 : c ∈ isoPartAlg π ρ := by rw [h]; trivial
    exact (iSup_le hall) h1
  exact hcne ((hPl c hc0).symm.trans this)

end Abstract

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

section Abstract

variable {G N X : Type} [Group G] [AddCommGroup N] [Module ℂ N] [AddCommGroup X] [Module ℂ X]
  {π : Representation ℂ G N} {ρ : Representation ℂ G X}

theorem le_biSup_of_fixed (hπ : π.IsIrreducible) (h : IsIsotypicAlg π ρ) {v : N} (hv : v ≠ 0) (Y : Submodule ℂ X)
    (hY : ∀ g, ∀ x ∈ Y, ρ g x ∈ Y) (s : Finset (π.IntertwiningMap ρ))
    (hF : ∀ x ∈ Y, (∀ g, π g v = v → ρ g x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap) :
    Y ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  haveI := isSemisimple_of_isotypic hπ h
  let A : Subrepresentation ρ := ⟨Y ⊓ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap, fun g x hx =>
    ⟨hY g x hx.1, stable_biSup s g x hx.2⟩⟩
  obtain ⟨C0, hc⟩ := exists_isCompl A
  let C : Subrepresentation ρ := ⟨Y ⊓ C0.toSubmodule, fun g x hx => ⟨hY g x hx.1, C0.apply_mem_toSubmodule g hx.2⟩⟩
  have hC : C = ⊥ := by
    by_contra hne
    obtain ⟨ψ, hi, hm⟩ := exists_intertwining_le hπ h C hne
    have hx0 : ψ v ≠ 0 := fun e => hv (hi (e.trans (map_zero ψ).symm))
    have hxY : ψ v ∈ Y := (hm v).1
    have hxM := hF _ hxY fun g hg => by rw [← ψ.isIntertwining, hg]
    have h1 : ψ v ∈ (A ⊓ C0).toSubmodule := ⟨⟨hxY, hxM⟩, (hm v).2⟩
    rw [hc.inf_eq_bot] at h1
    exact hx0 h1
  intro y hy
  have h2 : y ∈ (A ⊔ C0).toSubmodule := by rw [hc.sup_eq_top]; trivial
  obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1 h2
  have hcY : c ∈ Y := by simpa using Y.sub_mem hy ha.1
  have hcC : c ∈ C.toSubmodule := ⟨hcY, hc'⟩
  rw [hC] at hcC
  have hc0 : c = 0 := hcC
  rw [hc0, add_zero]
  exact ha.2

end Abstract

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

variable {D : D7} {V : HSp D} (u : HeightOneSpectrum (𝓞 D.host.F))

theorem finLoc_locFin (x : Gv V u) : finLoc V u (locFin V u x) = x :=
  proj_emb_self D.sp.cm.sig V.gram u x

theorem commute_locFin (x : Gv V u) {k : GfC V} (hk : finLoc V u k = 1) : Commute (locFin V u x) k :=
  Subtype.ext (commute_emb D.sp.cm.sig V.gram x hk).eq

theorem continuous_finLoc : Continuous (finLoc V u) :=
  (continuous_proj D.sp.cm.sig V.gram u).comp continuous_subtype_val

theorem continuous_locFin : Continuous (locFin V u) :=
  (continuous_emb D.sp.cm.sig V.gram u).subtype_mk _

noncomputable def away : GfC V →* GfC V where
  toFun k := k * (locFin V u (finLoc V u k))⁻¹
  map_one' := by simp
  map_mul' a b := by
    have hb : finLoc V u (b * (locFin V u (finLoc V u b))⁻¹) = 1 := by
      rw [map_mul, map_inv, finLoc_locFin, mul_inv_cancel]
    have hc := (commute_locFin u (finLoc V u a) hb).inv_left
    simp only [map_mul, mul_inv_rev]
    rw [mul_assoc a _ (b * _), hc.eq]
    simp only [mul_assoc]

theorem finLoc_away (k : GfC V) : finLoc V u (away u k) = 1 := by
  show finLoc V u (k * (locFin V u (finLoc V u k))⁻¹) = 1
  rw [map_mul, map_inv, finLoc_locFin, mul_inv_cancel]

theorem away_mul (k : GfC V) : away u k * locFin V u (finLoc V u k) = k := by
  show k * (locFin V u (finLoc V u k))⁻¹ * locFin V u (finLoc V u k) = k
  group

theorem continuous_away : Continuous (away (V := V) u) :=
  continuous_id.mul (((continuous_locFin u).comp (continuous_finLoc u)).inv)

end GlobalTheory.FinMultAway

namespace GlobalTheory.FinMultAway

theorem exists_finset_fixed_away : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))), ∀ x : W, (∀ k ∈ K, finLoc V u k = 1 → σ k x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  intro D V u W _ _ σ hσa N _ _ π hπ hπa hloc K hK
  have hiso : IsIsotypicAlg π (σ.comp (locFin V u)) := hloc
  obtain ⟨v, hv⟩ : ∃ v : N, v ≠ 0 := by
    by_contra hn
    push_neg at hn
    haveI : Subsingleton N := ⟨fun a b => (hn a).trans (hn b).symm⟩
    exact (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤) (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  let St : Subgroup (Gv V u) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {a b} ha hb => by
        show π (a * b) v = v
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        show π a⁻¹ v = v
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSt : IsOpen (St : Set (Gv V u)) := hπa.1 v
  obtain ⟨K0, hK0o, hK0c⟩ := GlobalTheory.CuspDec.exists_compact_open V
  let K2 : Subgroup (GfC V) := K0 ⊓ St.comap (finLoc V u) ⊓ K.comap (away u)
  have hK2o : IsOpen (K2 : Set (GfC V)) :=
    (hK0o.inter (hSt.preimage (continuous_finLoc u))).inter (hK.preimage (continuous_away u))
  have hK2c : IsCompact (K2 : Set (GfC V)) :=
    hK0c.of_isClosed_subset (K2.isClosed_of_isOpen hK2o) fun k hk => hk.1.1
  haveI := hσa.2 K2 hK2o hK2c
  let Y : Submodule ℂ W := GlobalTheory.PRep.fixed σ (K ⊓ (finLoc V u).ker)
  have hmemY : ∀ x, x ∈ Y ↔ ∀ k ∈ K, finLoc V u k = 1 → σ k x = x := by
    intro x
    rw [GlobalTheory.CuspDec.mem_fixed]
    exact ⟨fun h k hk h1 => h k ⟨hk, h1⟩, fun h k hk => h k hk.1 hk.2⟩
  have hY : ∀ g, ∀ x ∈ Y, σ.comp (locFin V u) g x ∈ Y := by
    intro g x hx
    rw [hmemY] at hx ⊢
    intro k hk h1
    show σ k (σ (locFin V u g) x) = σ (locFin V u g) x
    rw [← Module.End.mul_apply, ← map_mul, ← (commute_locFin u g h1).eq, map_mul, Module.End.mul_apply, hx k hk h1]
  let F : Submodule ℂ W := Y ⊓ GlobalTheory.PRep.fixed (σ.comp (locFin V u)) St
  have hFle : F ≤ GlobalTheory.PRep.fixed σ K2 := by
    intro y hy
    rw [GlobalTheory.CuspDec.mem_fixed]
    intro k hk
    have h1 : σ (locFin V u (finLoc V u k)) y = y := (GlobalTheory.CuspDec.mem_fixed.1 hy.2) _ hk.1.2
    have h2 : σ (away u k) y = y := (hmemY y).1 hy.1 _ hk.2 (finLoc_away u k)
    rw [← away_mul u k, map_mul, Module.End.mul_apply, h1, h2]
  haveI : FiniteDimensional ℂ F := Submodule.finiteDimensional_of_le hFle
  have hFfg : F.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨s, hs⟩ := IsCompactElement.exists_finset_of_le_iSup ((Submodule.fg_iff_compact F).1 hFfg)
    (fun φ : π.IntertwiningMap (σ.comp (locFin V u)) => LinearMap.range φ.toLinearMap)
    (le_of_le_of_eq le_top hiso.symm)
  refine ⟨s, fun x hx => le_biSup_of_fixed hπ hiso hv Y hY s (fun y hy hfix => hs ⟨hy, ?_⟩) ((hmemY x).2 hx)⟩
  exact GlobalTheory.CuspDec.mem_fixed.2 fun k hk => hfix k hk

end GlobalTheory.FinMultAway
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetLocalComponentCopiesFixedAwayStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_localComponent_copies_fixed_away : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))), ∀ x : W, (∀ k ∈ K, finLoc V u k = 1 → σ k x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  first | exact @GlobalTheory.FinMultAway.exists_finset_fixed_away | exact GlobalTheory.FinMultAway.exists_finset_fixed_away | (intros; apply GlobalTheory.FinMultAway.exists_finset_fixed_away <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorTraceEqConstMulLocalTrace
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.PureTensorTrace

theorem isIntegralOp_smoothOp {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
    [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X} (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ}
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ ρ f (smoothOp ρ μ f) := by
  intro v l
  have hi := hρ.smoothOp_integrand hf hc v
  refine ⟨?_, ?_⟩
  · have := integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
    simpa only [map_smul, smul_eq_mul] using this
  · rw [hρ.map_smoothOp (μ := μ) hf hc l v]
    simp only [smul_eq_mul]

theorem hasTrace_update_eq_const_mul : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ c : ℂ, ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, (∃ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf u) π f b) ∧ ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf u) π f b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V (Function.update ff u f)) (c * b) := by
  intro D V u μf hμ hK1 ν hν W _ _ σ hσ N _ _ π hπi hπa hloc ff hff
  haveI : (μf u).IsHaarMeasure := hμ u
  obtain ⟨H, K, hKo, hHc, hHf, hHop⟩ := GlobalTheory.T.pureTensorOperator_eq_offPlace_mul_atPlace D V u μf hμ hK1 ν hν W σ hσ.1 ff hff
  have hcont : Continuous (locFin V u) := (continuous_emb _ _ u).subtype_mk _
  have hρ : GlobalTheory.PRep.IsSmooth (σ.comp (locFin V u)) := fun x => (hσ.1 x).preimage hcont
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_finset_localComponent_copies_fixed_away D V u W σ hσ N π hπi hπa hloc K hKo
  have hrange : ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))),
      LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
    refine ⟨s, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hs _ fun k hk hk1 => hHf x k hk hk1
  have hschur : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id := fun φ =>
    GlobalTheory.T.schur_admissible_alt (Gv V u) (Kv V u) (isOpen_stabLoc _ _ _ u) (isCompact_stabLoc _ _ _ u) N π hπi hπa
      φ.toLinearMap fun g x => Representation.IntertwiningMap.isIntertwining _ _ φ g x
  obtain ⟨c, hc⟩ := GlobalTheory.T.trace_mul_endomorphism_isotypicRep (Gv V u) N W π (σ.comp (locFin V u)) hπi hschur hloc H
    (fun g x => hHc g x) hrange
  refine ⟨c, fun f hf => ⟨?_, ?_⟩⟩
  · have hfd := hπa.finiteDimensional_range_smoothOp (μ := μf u) hf.1 hf.2 (isOpen_stabLoc _ _ _ u)
      (isCompact_stabLoc _ _ _ u) (K := Kv V u)
    exact ⟨_, _, isIntegralOp_smoothOp hπa.1 hf.1 hf.2, hfd, rfl⟩
  · rintro b ⟨A, hA, hAb⟩
    obtain rfl := hA.unique (isIntegralOp_smoothOp hπa.1 hf.1 hf.2)
    have hB := isIntegralOp_smoothOp (μ := μf u) hρ hf.1 hf.2
    refine ⟨_, hHop f hf _ hB, hc _ _ (fun φ => ?_) b hAb⟩
    ext x
    exact (hπa.1.map_smoothOp_of_intertwining hρ hf.1 hf.2 φ.toLinearMap
      (fun g v => Representation.IntertwiningMap.isIntertwining _ _ φ g v) x).symm

end GlobalTheory.PureTensorTrace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorTraceEqConstMulLocalTraceStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_tensor_trace_eq_const_mul_local_trace : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ c : ℂ, ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, (∃ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf u) π f b) ∧ ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf u) π f b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V (Function.update ff u f)) (c * b) := by
  first | exact @GlobalTheory.PureTensorTrace.hasTrace_update_eq_const_mul | exact GlobalTheory.PureTensorTrace.hasTrace_update_eq_const_mul | (intros; apply GlobalTheory.PureTensorTrace.hasTrace_update_eq_const_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffEqZeroOfSumTraceProjectionsInequivalentIrre
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffEqZeroOfSumTraceProjectionsInequivalentIrre
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.TraceSep

theorem exists_smul_eq_ite {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, IsSimpleModule R (M i)]
    (h : ∀ i j, i ≠ j → ∀ f : M i →ₗ[R] M j, f = 0) (i₀ : ι) (s : ∀ i, Finset (M i)) :
    ∃ r : R, ∀ i, ∀ m ∈ s i, r • m = if i = i₀ then m else 0 := by
  first
  | exact @_root_.GlobalTheory.OrthogonalProjectionOnto.main
  | exact _root_.GlobalTheory.OrthogonalProjectionOnto.main
  | (apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.OrthogonalProjectionOnto.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OrthogonalProjectionOnto.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OrthogonalProjectionOnto.main ..)

end GlobalTheory.TraceSep

namespace GlobalTheory.TraceSep

theorem hasFinTrace_compress {V : Type} [AddCommGroup V] [Module ℂ V] (P : V →ₗ[ℂ] V) (hP : P ∘ₗ P = P)
    [FiniteDimensional ℂ (LinearMap.range P)] (A : V →ₗ[ℂ] V) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (P ∘ₗ A ∘ₗ P)
      (LinearMap.trace ℂ (LinearMap.range P) (P.rangeRestrict ∘ₗ A ∘ₗ (LinearMap.range P).subtype)) := by
  have hfix : ∀ u ∈ LinearMap.range P, P u = u := by
    rintro u ⟨w, rfl⟩; exact LinearMap.congr_fun hP w
  have hBU : LinearMap.range (P ∘ₗ A ∘ₗ P) ≤ LinearMap.range P := LinearMap.range_comp_le_range _ _
  haveI : FiniteDimensional ℂ (LinearMap.range (P ∘ₗ A ∘ₗ P)) := Submodule.finiteDimensional_of_le hBU
  refine ⟨inferInstance, ?_⟩
  have hQ : ∀ u, (P.rangeRestrict ∘ₗ A ∘ₗ (LinearMap.range P).subtype) u ∈
      (LinearMap.range (P ∘ₗ A ∘ₗ P)).comap (LinearMap.range P).subtype := by
    intro u
    refine ⟨u, ?_⟩
    simp [hfix u u.2]
  rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hQ,
    ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hBU)]
  congr 1
  ext ⟨x, hx⟩
  simp [LinearEquiv.conj_apply, Submodule.comapSubtypeEquivOfLe, hfix x (hBU hx)]

theorem coeff_eq_zero_of_sum_trace_eq_zero : ∀ (G : Type) [Group G] (n : ℕ) (W : Fin n → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), (∀ i, (σ i).IsIrreducible) → (∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))) → ∀ (P : ∀ i, W i →ₗ[ℂ] W i), (∀ i, P i ∘ₗ P i = P i) → (∀ i, FiniteDimensional ℂ (LinearMap.range (P i))) → ∀ a : Fin n → ℂ, (∀ (g : G) (c : Fin n → ℂ), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (P i ∘ₗ σ i g ∘ₗ P i) (c i)) → ∑ i, a i * c i = 0) → ∀ i, P i ≠ 0 → a i = 0 := by
  intro G _ n W _ _ σ hirr hne P hP hfin a hsum i₀ hi₀
  let Q : ∀ i, MonoidAlgebra ℂ G → Module.End ℂ (LinearMap.range (P i)) := fun i y =>
    (P i).rangeRestrict ∘ₗ (σ i).asAlgebraHom y ∘ₗ (LinearMap.range (P i)).subtype
  have hlin : ∀ y, ∑ i, a i * LinearMap.trace ℂ _ (Q i y) = 0 := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g =>
      refine hsum g _ fun i => ?_
      have := hasFinTrace_compress (P i) (hP i) (σ i g)
      simpa [Q, Representation.asAlgebraHom_of] using this
    | add x y hx hy =>
      simp only [Q, map_add (f := _), LinearMap.add_comp, LinearMap.comp_add, mul_add,
        Finset.sum_add_distrib] at hx hy ⊢
      rw [hx, hy, add_zero]
    | smul c x hx =>
      simp only [Q, map_smul, LinearMap.smul_comp, LinearMap.comp_smul, smul_eq_mul] at hx ⊢
      rw [Finset.sum_congr rfl fun i _ => mul_left_comm (a i) c _, ← Finset.mul_sum, hx, mul_zero]
  haveI : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (σ i).asModule := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp (hirr i)
  have hzero : ∀ i j, i ≠ j → ∀ f : (σ i).asModule →ₗ[MonoidAlgebra ℂ G] (σ j).asModule, f = 0 := by
    intro i j hij f
    haveI := hirr i
    haveI := hirr j
    haveI := hne i j hij
    haveI := (Representation.IntertwiningMap.equivLinearMapAsModule (σ i) (σ j)).toEquiv.symm.subsingleton
    exact Subsingleton.elim _ _
  let b : ∀ i, Module.Basis (Fin (Module.finrank ℂ (LinearMap.range (P i)))) ℂ (LinearMap.range (P i)) :=
    fun i => Module.finBasis ℂ _
  obtain ⟨x, hx⟩ := exists_smul_eq_ite (R := MonoidAlgebra ℂ G) (fun i => (σ i).asModule) hzero i₀
    (fun i => Finset.univ.image fun k => (((b i k : LinearMap.range (P i)) : W i) : (σ i).asModule))
  have hQx : ∀ i, Q i x = if i = i₀ then LinearMap.id else 0 := by
    intro i
    refine (b i).ext fun k => ?_
    have h1 := hx i _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    change (σ i).asAlgebraHom x (b i k : W i) = _ at h1
    have hfix : P i (b i k : W i) = b i k := by
      obtain ⟨w, hw⟩ := (b i k).2
      rw [← hw]; exact LinearMap.congr_fun (hP i) w
    apply Subtype.ext
    by_cases hi : i = i₀
    · subst hi
      have h1' : (σ i).asAlgebraHom x (b i k : W i) = b i k := by simpa using h1
      simp [Q, h1', hfix]
    · have h1' : (σ i).asAlgebraHom x (b i k : W i) = 0 :=
        h1.trans (if_neg hi)
      simp [Q, h1', hi]
  have h := hlin x
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [hQx i, if_neg hi, map_zero, mul_zero])
    (by simp)] at h
  rw [hQx i₀, if_pos rfl, LinearMap.trace_id] at h
  have hpos : 0 < Module.finrank ℂ (LinearMap.range (P i₀)) := by
    rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot, Ne, LinearMap.range_eq_bot]
    exact hi₀
  have hne0 : (Module.finrank ℂ (LinearMap.range (P i₀)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  exact (mul_eq_zero.1 h).resolve_right hne0

end GlobalTheory.TraceSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoeffEqZeroOfSumTraceProjectionsInequivalentIrreStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_sum_trace_projections_inequivalent_irreps : ∀ (G : Type) [Group G] (n : ℕ) (W : Fin n → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (σ : ∀ i, Representation ℂ G (W i)), (∀ i, (σ i).IsIrreducible) → (∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))) → ∀ (P : ∀ i, W i →ₗ[ℂ] W i), (∀ i, P i ∘ₗ P i = P i) → (∀ i, FiniteDimensional ℂ (LinearMap.range (P i))) → ∀ a : Fin n → ℂ, (∀ (g : G) (c : Fin n → ℂ), (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace (P i ∘ₗ σ i g ∘ₗ P i) (c i)) → ∑ i, a i * c i = 0) → ∀ i, P i ≠ 0 → a i = 0 := by
  first | exact @GlobalTheory.TraceSep.coeff_eq_zero_of_sum_trace_eq_zero | exact GlobalTheory.TraceSep.coeff_eq_zero_of_sum_trace_eq_zero | (intros; apply GlobalTheory.TraceSep.coeff_eq_zero_of_sum_trace_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTrace
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical

noncomputable section

namespace GlobalTheory.TrMultSep

theorem separation_of_iwahoriTrace (hI : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace) (hE : GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate) :
    Separation := by
  intro D V T U hU μf hμ hK ν hν n Ws _ _ σs hσ a hyp
  haveI : ν.IsHaarMeasure := hν.1
  obtain ⟨e, he, hP, hfam⟩ := GlobalTheory.T.exists_testFamilies_projectedTranslationOperators D V T U hU μf hμ hK ν hν
  have hex : ∀ i, ∃ P : Ws i →ₗ[ℂ] Ws i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν (σs i) (finFn V e) P ∧
      FiniteDimensional ℂ (LinearMap.range P) := by
    intro i
    obtain ⟨c, A, hA, hAf⟩ := (GlobalTheory.T.admissibleRep_hasTrace_finiteAdelicPureTensorFunction D V ν e he (Ws i) (σs i) (hσ.2.1 i)).1
    exact ⟨A, hA, hAf.1⟩
  choose P hPint using hex
  have hidem : ∀ i, P i ∘ₗ P i = P i := fun i => (hP (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1).1
  have hne : ∀ i, HasTypeVec T (σs i) → P i ≠ 0 := fun i h => (hP (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1).2 h
  intro i hi
  refine GlobalTheory.T.coeff_eq_zero_of_sum_trace_projections_inequivalent_irreps (GfC V) n Ws σs hσ.1 hσ.2.2 P hidem (fun i => (hPint i).2) a ?_ i (hne i hi)
  intro g c hc
  obtain ⟨ff, hff, hffI, hffT, hffOp⟩ := hfam g
  have htr : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i) := fun i =>
    ⟨_, hffOp (Ws i) (σs i) (hσ.2.1 i).1 (P i) (hPint i).1, hc i⟩
  have hloc := fun i => GlobalTheory.T.exists_irreducible_admissible_localComponent_finiteAdelic D V U.u (Ws i) (σs i) (hσ.1 i) (hσ.2.1 i)
  choose N instA instM π hπ using hloc
  letI : ∀ i, AddCommGroup (N i) := instA
  letI : ∀ i, Module ℂ (N i) := instM
  have hfac := fun i => GlobalTheory.T.pure_tensor_trace_eq_const_mul_local_trace D V U.u μf hμ hK ν hν (Ws i) (σs i) (hσ.2.1 i) (N i) (π i) (hπ i).1
    (hπ i).2.1 (hπ i).2.2 ff hff
  choose c' hc' using hfac
  have hd : ∀ t ∈ strictTorus V.rank U.ϖ, ∀ b : Fin n → ℂ,
      (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf U.u) (π i) (U.frame.cosetFn t) (b i)) →
      ∑ i, (a i * c' i) * b i = 0 := by
    intro t ht b hb
    have h := hyp (Function.update ff U.u (U.frame.cosetFn t)) (hffT t ht).1 (hffT t ht).2 (fun i => c' i * b i)
      (fun i => (hc' i _ (U.frame.cosetFn_mem t)).2 (b i) (hb i))
    simpa [mul_assoc] using h
  have hb := fun i => (hc' i (ff U.u) (hff.1 U.u)).1
  choose b hb using hb
  have key := GlobalTheory.T.admissible_irreducible_torus_characters hI hE D V U (μf U.u) (hμ U.u) n N π (fun i => (hπ i).1) (fun i => (hπ i).2.1)
    (fun i => a i * c' i) hd (ff U.u) (hff.1 U.u) hffI b hb
  have hceq : ∀ i, c i = c' i * b i := by
    intro i
    have h := (hc' i (ff U.u) (hff.1 U.u)).2 (b i) (hb i)
    rw [Function.update_eq_self] at h
    exact (htr i).unique h
  simp_rw [hceq, ← mul_assoc]
  exact key

end GlobalTheory.TrMultSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTraceStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_separation_of_iwahori_trace : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → Separation := by
  first | exact @GlobalTheory.TrMultSep.separation_of_iwahoriTrace | exact GlobalTheory.TrMultSep.separation_of_iwahoriTrace | (intros; apply GlobalTheory.TrMultSep.separation_of_iwahoriTrace <;> assumption)
end
