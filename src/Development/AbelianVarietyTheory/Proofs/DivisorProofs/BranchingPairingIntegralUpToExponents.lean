module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineTheta
public import Formalism.LocalToGlobal.Divisibility.BrJoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateSubstLinearEquivSymmMemNabla
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateSubstLinearEquivSymmMemNabla
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem funEquiv_symm_mem_nabAt_of_nabAtr : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (σ : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E M → ∀ (v : VV K fun τ => (σ τ).dual),
    v ∈ nabAtr emb (fun τ => (σ τ).dual) M → (GlobalTheory.FunObj.funEquiv σ).symm v ∈ nabAt emb σ M := by
  intro E K ι _ _ _ _ _ emb n σ M hM v hv
  have hA : ∀ τ, (tauLat emb τ M).FG := by
    classical
    intro τ
    obtain ⟨S, hS⟩ := hM.fg
    rw [Formalism.L2.DIV.du_tauLat_eq, ← hS, Formalism.L2.DIV.du_tl_span]
    exact ⟨S.image (Formalism.L2.DIV.du_f (emb τ)), by rw [Finset.coe_image]⟩
  change ((GlobalTheory.FunObj.funEquiv σ).symm v).1 ∈ nabP σ (fun τ => tauLat emb τ M)
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap]
  intro w B hB
  have hB' : ∀ τ, IsBasisAt w (dualFr (tauLat emb τ M)) (invTrK B τ) := fun τ =>
    GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hA τ) (hB τ)
  have h1 : v.1 ∈ nabP (fun τ => (σ τ).dual) (fun τ => dualFr (tauLat emb τ M)) := hv
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap] at h1
  have h2 := h1 w (invTrK B) hB'
  rw [← map_inv] at h2
  obtain ⟨s, hs, hsv⟩ := (Formalism.L2.DIV.lc_mem_locP w _ _).1 h2
  refine (Formalism.L2.DIV.lc_mem_locP w _ _).2 ⟨s, hs, ?_⟩
  set F := (GlobalTheory.FunObj.funEquiv σ).symm v with hF
  have e2 : GlobalTheory.FunObj.funEquiv σ (s • rhoK σ B⁻¹ F) = s • rhoK (fun τ => (σ τ).dual) (invTrK B⁻¹) v := by
    rw [LinearMapClass.map_smul_of_tower, GlobalTheory.FunObj.funEquiv_rhoK, hF, LinearEquiv.apply_symm_apply]
  have h3 : (s • rhoK σ B⁻¹ F).1 ∈ nabStd K σ := by
    rw [GlobalTheory.FunObj.funEquiv_mem_nabStd, e2]
    exact hsv
  exact h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjugateSubstLinearEquivSymmMemNablaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjugateSubstLinearEquiv_symm_mem_nabla : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n : ℕ} (σ : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsLattice E M → ∀ (v : VV K fun τ => (σ τ).dual),
    v ∈ nabAtr emb (fun τ => (σ τ).dual) M → (GlobalTheory.FunObj.funEquiv σ).symm v ∈ nabAt emb σ M := by
  first | exact @GlobalTheory.funEquiv_symm_mem_nabAt_of_nabAtr | exact GlobalTheory.funEquiv_symm_mem_nabAt_of_nabAtr | (intros; apply GlobalTheory.funEquiv_symm_mem_nabAt_of_nabAtr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfLastCoordinateExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfLastCoordinateExtension
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem latLast_isLattice : ∀ {E : Type} [Field E] [NumberField E] {n N : ℕ} (hN : N = n + 1)
    (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    Submodule.IsLattice E L := by
  intro E _ _ n N hN M L hM hL
  subst hN
  have hiC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => Fin.ext rfl
  have hiL : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := Fin.ext rfl
  simp only [hiC, hiL] at hL
  let g : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) :=
    { toFun := fun x => Fin.snoc (α := fun _ => E) x 0
      map_add' := by
        intro x y; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
      map_smul' := by
        intro a x; ext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp }
  have gC : ∀ x k, g x (Fin.castSucc k) = x k := fun x k => by simp [g]
  have gL : ∀ x, g x (Fin.last n) = 0 := fun x => by simp [g]
  let e : Fin (n + 1) → E := Pi.single (Fin.last n) 1
  have gm : ∀ m ∈ M, g m ∈ L := fun m hm => (hL _).2 ⟨by simpa [gC] using hm, 0, by simp [gL]⟩
  have he : e ∈ L := (hL _).2 ⟨by
      have : (fun k : Fin n => e (Fin.castSucc k)) = 0 := by
        funext k; simp [e, Pi.single_apply, Fin.castSucc_ne_last]
      rw [this]; exact M.zero_mem, 1, by simp [e]⟩
  have dec : ∀ x : Fin (n + 1) → E, x = g (fun k => x (Fin.castSucc k)) + x (Fin.last n) • e := by
    intro x; ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [gL, e]
    · simp [gC, e, Pi.single_apply, Fin.castSucc_ne_last]
  have hLeq : L = M.map (g.restrictScalars (𝓞 E)) ⊔ Submodule.span (𝓞 E) {e} := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hvM, c, hc⟩ := (hL v).1 hv
      rw [dec v]
      refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_map_of_mem hvM))
        (Submodule.mem_sup_right ?_)
      have hs : (c : E) • e = c • e := algebraMap_smul E c e
      rw [← hc, hs]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)
    · exact sup_le (Submodule.map_le_iff_le_comap.2 fun m hm => gm m hm)
        (Submodule.span_le.2 (by simpa using he))
  refine ⟨?_, ?_⟩
  · rw [hLeq]
    exact Submodule.FG.sup (hM.fg.map _) (Submodule.fg_span_singleton e)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfLastCoordinateExtensionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_of_lastCoordinate_extension : ∀ {E : Type} [Field E] [NumberField E] {n N : ℕ} (hN : N = n + 1)
    (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    Submodule.IsLattice E L := by
  first | exact @GlobalTheory.latLast_isLattice | exact GlobalTheory.latLast_isLattice | (intros; apply GlobalTheory.latLast_isLattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeEmbeddedLastCoordinateSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeEmbeddedLastCoordinateSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open Formalism.L2.Col

theorem mem_dualFr_span_iff_dualsum {K : Type} [Field K] [NumberField K] {n : ℕ} (S : Set (Fin n → K))
    (φ : Fin n → K) :
    φ ∈ dualFr (Submodule.span (𝓞 K) S) ↔ ∀ x ∈ S, φ ⬝ᵥ x ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro h x hx
    exact h x (Submodule.subset_span hx)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => rw [dotProduct_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [dotProduct_add]; exact add_mem hx hy
    | smul a x _ hx => rw [dotProduct_smul]; exact Submodule.smul_mem _ a hx

theorem dualFr_tauLat_sumLat : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n N : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 E) (Fin n → E))
    (L : Submodule (𝓞 E) (Fin N → E)),
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ τ : ι, dualFr (tauLat emb τ L) = Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) 1 := by
  intro E K ι _ _ _ _ _ emb n N hN M L hL τ
  subst hN
  have hC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => rfl
  have hLst : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  have split : ∀ φ x : Fin (n + 1) → K, φ ⬝ᵥ x = (fun k => φ (Fin.castSucc k)) ⬝ᵥ (fun k => x (Fin.castSucc k))
      + φ (Fin.last n) * x (Fin.last n) := by
    intro φ x
    simp only [dotProduct, Fin.sum_univ_castSucc]
  ext φ
  rw [tauLat, mem_dualFr_span_iff_dualsum]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [tauLat, mem_dualFr_span_iff_dualsum]
      rintro _ ⟨m, hm, rfl⟩
      let v : Fin (n + 1) → E := Fin.lastCases 0 m
      have hv : v ∈ L := by
        rw [hL]
        refine ⟨?_, 0, ?_⟩
        · simpa [hC, v] using hm
        · simp [hLst, v]
      have := h _ ⟨v, hv, rfl⟩
      rw [split] at this
      simpa [hC, v] using this
    · let v : Fin (n + 1) → E := Pi.single (Fin.last n) 1
      have hv : v ∈ L := by
        rw [hL]
        refine ⟨?_, 1, ?_⟩
        · have : (fun k : Fin n => v (Formalism.L2.Col.Br.iC rfl k)) = 0 := by
            funext k; simp [hC, v, Fin.castSucc_ne_last]
          rw [this]; exact M.zero_mem
        · simp [hLst, v]
      have := h _ ⟨v, hv, rfl⟩
      rw [split] at this
      have h0 : (fun k : Fin n => (fun a => emb τ (v a)) (Fin.castSucc k)) = 0 := by
        funext k; simp [v, Fin.castSucc_ne_last]
      rw [h0, dotProduct_zero, zero_add] at this
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 this
      refine ⟨c, ?_⟩
      rw [hLst, mul_one]
      have hv1 : (fun (x : Fin (n + 1) → E) a => emb τ (x a)) v (Fin.last n) = 1 := by simp [v]
      rw [hv1, mul_one] at hc
      rw [← hc]
  · rintro ⟨h1, c, hc⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, hL] at hv
    obtain ⟨hvM, d, hd⟩ := hv
    rw [split]
    refine add_mem ?_ ?_
    · rw [tauLat, mem_dualFr_span_iff_dualsum] at h1
      have := h1 _ ⟨_, hvM, rfl⟩
      simpa [hC] using this
    · rw [hLst] at hc hd
      refine Submodule.mem_one.2 ⟨c * RingOfIntegers.mapRingHom (emb τ) d, ?_⟩
      rw [map_mul, hc, mul_one]
      show _ = _ * emb τ (v (Fin.last n))
      rw [← hd]
      rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeEmbeddedLastCoordinateSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_embedded_lastCoordinate_sum : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι]
    (emb : ι → E →+* K) {n N : ℕ} (hN : N = n + 1) (M : Submodule (𝓞 E) (Fin n → E))
    (L : Submodule (𝓞 E) (Fin N → E)),
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ τ : ι, dualFr (tauLat emb τ L) = Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) 1 := by
  first | exact @GlobalTheory.dualFr_tauLat_sumLat | exact GlobalTheory.dualFr_tauLat_sumLat | (intros; apply GlobalTheory.dualFr_tauLat_sumLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingIntegralUpToExponents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BrPairLocal

theorem finLocal : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) {n N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsFullLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    u ∈ nabAtr emb Λ L → v ∈ nabAtr emb (fun τ => (σ τ).dual) M →
    GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0 ∨
      -Formalism.DivisionValues.vw w (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≤
        Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro E K ι _ _ _ _ _ _ emb n N hN Λ σ hI hS M L hM hL w u v hu hv
  have hLlat : Submodule.IsFullLattice E L := by
    haveI : Submodule.IsLattice E L := GlobalTheory.T.isLattice_of_lastCoordinate_extension hN M L hM.toIsLattice hL
    refine ⟨?_⟩
    subst hN
    have hiC : ∀ k : Fin n, Formalism.L2.Col.Br.iC (rfl : n + 1 = n + 1) k = Fin.castSucc k := fun k => Fin.ext rfl
    have hiL : Formalism.L2.Col.Br.iL (rfl : n + 1 = n + 1) = Fin.last n := Fin.ext rfl
    simp only [hiC, hiL] at hL
    let g : (Fin n → E) →ₗ[E] (Fin (n + 1) → E) :=
      { toFun := fun x => Fin.snoc (α := fun _ => E) x 0
        map_add' := by intro x y; ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
        map_smul' := by intro a x; ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp }
    let e : Fin (n + 1) → E := Pi.single (Fin.last n) 1
    have gm : ∀ m ∈ M, g m ∈ L := fun m hm => (hL _).2 ⟨by simpa [g] using hm, 0, by simp [g]⟩
    have he : e ∈ L := (hL _).2 ⟨by
      have : (fun k : Fin n => e (Fin.castSucc k)) = 0 := by
        funext k; simp [e, Pi.single_apply, Fin.castSucc_ne_last]
      rw [this]; exact M.zero_mem, 1, by simp [e]⟩
    have hg : ∀ x : Fin n → E, g x ∈ Submodule.span E (L : Set (Fin (n + 1) → E)) := by
      intro x
      have hx : x ∈ Submodule.span E (M : Set (Fin n → E)) := by rw [hM.span_eq_top]; trivial
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (gm x hx)
      | zero => simp
      | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
      | smul a x hx ih => simpa using Submodule.smul_mem _ a ih
    apply top_unique
    intro x _
    have dec : x = g (fun k => x (Fin.castSucc k)) + x (Fin.last n) • e := by
      ext j; refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [g, e, Pi.single_apply, Fin.castSucc_ne_last]
    rw [dec]
    exact Submodule.add_mem _ (hg _) (Submodule.smul_mem _ _ (Submodule.subset_span he))
  have h1 := GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr E K ι N emb Λ L hLlat w u hu
  obtain ⟨s, hs, hsu⟩ := (Formalism.L2.DIV.lc_mem_locP w _ _).1 h1
  have hdel : delAtr emb Λ L = delK Λ (fun τ => Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) (1 : K)) := by
    unfold delAtr
    congr 1
    funext τ
    exact GlobalTheory.T.dualLattice_embedded_lastCoordinate_sum emb hN M L hL τ
  rw [hdel] at hsu
  have h2 := GlobalTheory.BranchFormula.integrality Formalism.L2.DIV.BrJ.branching_interlacing_pairs K ι N n hN Λ σ hI hS
    (fun τ => dualFr (tauLat emb τ M)) (fun _ => 1) (fun _ => one_ne_zero) _ hsu
  have hbr : Formalism.L2.Col.Br.brAt hN Λ σ (fun _ => (1 : K)) = Formalism.L2.Col.Br.brStd hN Λ σ := by
    simp [Formalism.L2.Col.Br.brAt]
  rw [hbr] at h2
  have hy := GlobalTheory.T.adjugateSubstLinearEquiv_symm_mem_nabla emb σ M hM.toIsLattice v hv
  have h3 := ((Formalism.L2.DIV.pairBDual E K ι n emb σ M hM _).1.1 h2) _ hy
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h3
  have key : (s : K) * (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) *
      GlobalTheory.BrPairF.brPairF σ hN Λ u v = (r : K) := by
    have e1 : (r : K) = algebraMap (𝓞 K) K r := rfl
    rw [e1, hr, GlobalTheory.BrPairF.brPairF_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
      LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.smul_apply,
      Algebra.smul_def, Algebra.smul_def, map_pow, map_natCast, mul_assoc]
  by_cases hP : GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0
  · exact Or.inl hP
  right
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]
    exact w.asIdeal.zero_mem
  have hp0 : (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Formalism.EigenvalueLevelCeiling.plc_prime w).ne_zero)
  have h4 := Formalism.DivisionValues.ReductionFirst.vw_int_nonneg w r
  rw [← key, Formalism.DivisionValues.ReductionFirst.vw_mul w (mul_ne_zero hs0 hp0) hP, Formalism.DivisionValues.ReductionFirst.vw_mul w hs0 hp0,
    Formalism.DivisionValues.ReductionFirst.vw_unit w s hs] at h4
  linarith

end GlobalTheory.BrPairLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingIntegralUpToExponentsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branchingPairing_integral_upToExponents : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) {n N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsFullLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    u ∈ nabAtr emb Λ L → v ∈ nabAtr emb (fun τ => (σ τ).dual) M →
    GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0 ∨
      -Formalism.DivisionValues.vw w (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≤
        Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro E K ι _ _ _ _ _ _ emb n N hN Λ σ hI hS M L hM hL w u v hu hv
  first
  | exact GlobalTheory.BrPairLocal.finLocal emb hN Λ σ hI hS M L hM hL w u v hu hv
  | exact GlobalTheory.BrPairLocal.finLocal emb hN Λ σ hI hS M L hM.toIsLattice hL w u v hu hv
end
