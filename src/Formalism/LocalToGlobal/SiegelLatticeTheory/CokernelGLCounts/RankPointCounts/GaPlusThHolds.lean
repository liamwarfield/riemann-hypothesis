module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GaCongG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NotIntDensOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegralityUnderRingMap.MemIntegerOfIsIntegralMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefDensTh

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.HaarIdx
noncomputable section

open scoped Classical
open ValuativeRel MeasureTheory

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Split

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem R_eq_O_of_none {M : Model F E} (h : M.split = none) : M.R = M.L.O := by
  unfold Model.R
  rw [h]

end Split

end PI.NGStepBBW
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CrossOfComp
noncomputable section

open Matrix ValuativeRel
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal Formalism.L2.SG.Pf.PCount
  Formalism.L2.SG.LsDatumB

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem cross_of_comp {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L) {r : ℕ} {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (h1 : Cross (A.map (π1 M g)) (A'.map (π1 M g))) (h2 : Cross (A.map (π2 M g)) (A'.map (π2 M g))) : Cross A A' := by
  unfold Cross at h1 h2 ⊢
  have d : ∀ (f : E →+* F) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (B.map f).det = f B.det :=
    fun f B => (RingHom.map_det f B).symm
  rw [ld_map, ld_map, d, d, ← map_mul, ← map_mul] at h1 h2
  apply g.e.injective
  exact Prod.ext h1 h2

theorem gaPlusTh_of (hLO : LiftOrb) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) : GaPlusTh M δ u u' := by
  intro hA hT hPH w w' Z Z' hk hZ hZ' p hne heq
  set c := cornerSh δ (D.mem u).A.T (D.mem u').A.T p w with hc
  have hc' : cornerSh δ (D.mem u).A.T (D.mem u').A.T p w' = c := (cornerSh_of_kind δ _ _ p hk).symm
  set Y := CntLocal.ZZP (M := M) δ u u' p Z + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY
  set Y' := CntLocal.ZZP (M := M) δ u u' p Z' + c • Ec (K := (D.s.atP p).Ep) D.R.rS with hY'
  have hcm : ∀ cc : (D.s.atP p).Ep, (Matrix.of fun a b : Fin (D.R.rS + 1) =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cc else 0) = cc • Ec (K := (D.s.atP p).Ep) D.R.rS := by
    intro cc; ext a b; simp only [Ec, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]; split_ifs <;> simp
  have eY : FCount.thZ M δ u u' w Z p = clsOf (M p) Y := by
    unfold FCount.thZ thL; rw [hcm]
  have eY' : FCount.thZ M δ u u' w' Z' p = clsOf (M p) Y' := by
    unfold FCount.thZ thL; rw [hcm, hc']
  rw [eY] at hne heq
  rw [eY'] at heq

  have hXc : Cross (ZhatLoc M δ p Z) (ZhatLoc M δ p Z') := cross_zhatLoc δ M p (cross_global hk hZ hZ')
  have hZc : Cross (CntLocal.ZZP (M := M) δ u u' p Z) (CntLocal.ZZP (M := M) δ u u' p Z') := by
    unfold CntLocal.ZZP
    rcases hs : (M p).split with _ | g
    · unfold Loc.HermSp.ZZplusOf; rw [hs]; exact hXc
    · refine cross_of_comp (M p) g ?_ ?_
      · rw [zzPlus_map_firstComponent (M p) g hs, zzPlus_map_firstComponent (M p) g hs]
        exact cross_shift (cross_map _ hXc) _ _
      · rw [zzPlus_map_secondComponent (M p) g hs, zzPlus_map_secondComponent (M p) g hs]
        exact cross_shift (cross_transpose (cross_map _ hXc)) _ _
  unfold clsOf at hne heq
  by_cases h1 : (∀ a b, Y a b ∈ (M p).R) ∧ IsUnit Y.det
  swap
  · exact absurd (dif_neg h1) hne
  rw [dite_eq_left h1] at heq
  by_cases h2 : (∀ a b, Y' a b ∈ (M p).R) ∧ IsUnit Y'.det
  swap
  · rw [dif_neg h2] at heq; exact absurd heq (by simp)
  rw [dite_eq_left h2] at heq
  set ZZ : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y a b, h1.1 a b⟩, h1.2⟩ with hZZ
  set ZZ' : (M p).Mat (D.R.rS + 1) := ⟨Matrix.of fun a b => ⟨Y' a b, h2.1 a b⟩, h2.2⟩ with hZZ'
  have hmap : ZZ.Z.map (M p).R.subtype = Y := rfl
  have hmap' : ZZ'.Z.map (M p).R.subtype = Y' := rfl
  have hiso : Nonempty ((M p).Iso ZZ ZZ') := Quotient.exact (Option.some.inj heq)
  have hκ : (ZZ.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) =
      (ZZ'.Z.map (M p).R.subtype)⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) := by
    rw [hmap, hmap']
    exact kappa_eq hZc c h1.2 h2.2
  obtain ⟨l, ρ, hlu, hρu, hle, hρl, hrel⟩ := hLO (M p) (hA p).1 D.R.rS ZZ ZZ' hiso hκ
  set L := l.map (M p).R.subtype with hLdef
  set P := ρ.map (M p).R.subtype with hPdef
  have hL : ∀ i, L i (Fin.last D.R.rS) = if i = Fin.last D.R.rS then 1 else 0 := by
    intro i; simp only [hLdef, Matrix.map_apply, hle i]; split_ifs <;> simp
  have hP : ∀ j, P (Fin.last D.R.rS) j = if j = Fin.last D.R.rS then 1 else 0 := by
    intro j; simp only [hPdef, Matrix.map_apply, hρl j]; split_ifs <;> simp
  have hYrel : Y' = L * Y * P := by
    rw [← hmap, ← hmap', hrel, Matrix.map_mul, Matrix.map_mul]
  have hZrel : CntLocal.ZZP (M := M) δ u u' p Z' = L * CntLocal.ZZP (M := M) δ u u' p Z * P := by
    have e := hYrel
    rw [hY, hY', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Ec_eq_cornerM,
      corner_sandwich L P hL hP 1] at e
    exact add_right_cancel e
  have hLR : ∀ i j, L i j ∈ (M p).R := fun i j => (l i j).2
  have hPR : ∀ i j, P i j ∈ (M p).R := fun i j => (ρ i j).2
  have hLu : ∃ y ∈ (M p).R, L.det * y = 1 := by
    obtain ⟨v, hv⟩ := hlu
    refine ⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩
    have : L.det = ((l.det : (M p).R) : (D.s.atP p).Ep) := (RingHom.map_det (M p).R.subtype l).symm
    rw [this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  have hPu : ∃ y ∈ (M p).R, P.det * y = 1 := by
    obtain ⟨v, hv⟩ := hρu
    refine ⟨((v⁻¹ : (M p).Rˣ) : (M p).R), ((v⁻¹ : (M p).Rˣ) : (M p).R).2, ?_⟩
    have : P.det = ((ρ.det : (M p).R) : (D.s.atP p).Ep) := (RingHom.map_det (M p).R.subtype ρ).symm
    rw [this, ← hv, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rcases hs : (M p).split with _ | g
  · have hRO : (M p).R = (M p).L.O := by unfold Loc.Model.R; rw [hs]
    have hX : ZhatLoc M δ p Z' = L * ZhatLoc M δ p Z * P := by
      have e := hZrel
      unfold CntLocal.ZZP Loc.HermSp.ZZplusOf at e
      rw [hs] at e
      exact e
    obtain ⟨yL, hyL, hLy⟩ := hLu
    obtain ⟨yP, hyP, hPy⟩ := hPu
    exact gaCong_L δ M hA p hs _ _ Z Z' L P hL hP (fun i j => hRO ▸ hLR i j) (fun i j => hRO ▸ hPR i j)
      ⟨yL, hRO ▸ hyL, hLy⟩ ⟨yP, hRO ▸ hyP, hPy⟩ hX
  · exact gaCong_G δ M hA p g hs _ _ _ _ Z Z' L P hL hP hLR hPR hLu hPu hZrel

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLiftFin
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLiftM
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SRLiftGen
noncomputable section

namespace Formalism.L2.SG.Pf.SRL

open Matrix Module

section Compl

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem exists_isCompl_mem {U : Submodule k V} {e : V} (h : Disjoint U (k ∙ e)) :
    ∃ C : Submodule k V, IsCompl U C ∧ e ∈ C := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (U ⊔ k ∙ e)
  refine ⟨k ∙ e ⊔ W, ⟨h.disjoint_sup_right_of_disjoint_sup_left hW.disjoint, ?_⟩,
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self e)⟩
  rw [codisjoint_iff, ← sup_assoc]
  exact hW.sup_eq_top

theorem exists_isCompl_le {R' K : Submodule k V} (h : R' ⊔ K = ⊤) : ∃ W : Submodule k V, IsCompl R' W ∧ W ≤ K := by
  obtain ⟨W0, hW0⟩ := Submodule.exists_isCompl (R' ⊓ K)
  refine ⟨W0 ⊓ K, ⟨?_, ?_⟩, inf_le_right⟩
  · rw [disjoint_iff, eq_bot_iff, ← hW0.inf_eq_bot]
    exact le_inf (inf_le_inf_left _ inf_le_right) (inf_le_right.trans inf_le_left)
  · have hm : (R' ⊓ K) ⊔ (W0 ⊓ K) = K := by
      rw [← sup_inf_assoc_of_le W0 (inf_le_right : R' ⊓ K ≤ K), hW0.sup_eq_top, top_inf_eq]
    rw [codisjoint_iff, eq_top_iff, ← h]
    refine sup_le le_sup_left ?_
    calc K = (R' ⊓ K) ⊔ (W0 ⊓ K) := hm.symm
      _ ≤ R' ⊔ (W0 ⊓ K) := sup_le_sup_right inf_le_left _

end Compl

section Field

variable {k : Type*} [Field k] {n : ℕ}

theorem srLift_field (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (K : Submodule k (Fin (n + 1) → k))
    (hA : ∀ i, A i (Fin.last n) = if i = Fin.last n then 1 else 0)
    (hK : ∀ v, ∃ x, v - A *ᵥ x ∈ K) :
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) k, (∀ j, (fun i => H i j) ∈ K) ∧ (∀ i, H i (Fin.last n) = 0) ∧
      (A + H).det ≠ 0 := by
  classical
  have he : A *ᵥ Pi.single (Fin.last n) 1 = Pi.single (Fin.last n) 1 := by
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hA]
  have hRK : LinearMap.range A.mulVecLin ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, hx⟩ := hK v
    rw [show v = A *ᵥ x + (v - A *ᵥ x) by abel]
    exact Submodule.add_mem_sup (LinearMap.mem_range.2 ⟨x, Matrix.mulVecLin_apply A x⟩) hx
  obtain ⟨W, hW, hWK⟩ := exists_isCompl_le hRK
  have hdisj : Disjoint (LinearMap.ker A.mulVecLin) (k ∙ (Pi.single (Fin.last n) 1 : Fin (n + 1) → k)) := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx2
    rw [LinearMap.mem_ker, map_smul, Matrix.mulVecLin_apply, he] at hx1
    exact hx1
  obtain ⟨C, hC, heC⟩ := exists_isCompl_mem hdisj
  have hdim : finrank k (LinearMap.ker A.mulVecLin) = finrank k W := by
    have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    omega
  let φ := LinearEquiv.ofFinrankEq _ _ hdim
  let h : (Fin (n + 1) → k) →ₗ[k] (Fin (n + 1) → k) :=
    W.subtype ∘ₗ φ.toLinearMap ∘ₗ (LinearMap.ker A.mulVecLin).projectionOnto C hC
  have hHv : ∀ v, LinearMap.toMatrix' h *ᵥ v = h v := fun v => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  refine ⟨LinearMap.toMatrix' h, fun j => ?_, fun i => ?_, ?_⟩
  · have hc : (fun i => LinearMap.toMatrix' h i j) = h (Pi.single j 1) := by
      funext i
      rw [LinearMap.toMatrix'_apply]
    rw [hc]
    exact hWK (φ _).2
  · have h0 : (LinearMap.ker A.mulVecLin).projectionOnto C hC (Pi.single (Fin.last n) 1) = 0 :=
      Submodule.linearProjOfIsCompl_apply_right hC ⟨_, heC⟩
    rw [LinearMap.toMatrix'_apply]
    simp only [h, LinearMap.comp_apply, h0, LinearMap.map_zero, Pi.zero_apply]
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hv0
    rw [Matrix.add_mulVec, hHv] at hv
    have hvt : v ∈ LinearMap.ker A.mulVecLin ⊔ C := by rw [hC.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, c, hc, rfl⟩ := Submodule.mem_sup.1 hvt
    have hfx : A *ᵥ x = 0 := by
      rw [← Matrix.mulVecLin_apply]
      exact LinearMap.mem_ker.1 hx
    have hproj : (LinearMap.ker A.mulVecLin).projectionOnto C hC (x + c) = ⟨x, hx⟩ := by
      rw [map_add (f := _), Submodule.linearProjOfIsCompl_apply_left hC ⟨x, hx⟩,
        Submodule.linearProjOfIsCompl_apply_right hC ⟨c, hc⟩, add_zero]
    have hv' : A *ᵥ c + (φ ⟨x, hx⟩ : Fin (n + 1) → k) = 0 := by
      have e : h (x + c) = (φ ⟨x, hx⟩ : Fin (n + 1) → k) := by
        simp only [h, LinearMap.comp_apply, hproj]
        rfl
      rw [Matrix.mulVec_add, hfx, zero_add, e] at hv
      exact hv
    have hz : A *ᵥ c = 0 := by
      refine Submodule.disjoint_def.1 hW.disjoint _
        (LinearMap.mem_range.2 ⟨c, Matrix.mulVecLin_apply A c⟩) ?_
      rw [eq_neg_of_add_eq_zero_left hv']
      exact W.neg_mem (φ _).2
    have hφ : φ ⟨x, hx⟩ = 0 := by
      rw [hz, zero_add] at hv'
      exact Subtype.ext hv'
    have hx0 : x = 0 := by
      have := congrArg Subtype.val (φ.map_eq_zero_iff.1 hφ)
      simpa using this
    have hc0 : c = 0 := Submodule.disjoint_def.1 hC.disjoint c
      (LinearMap.mem_ker.2 (by rw [Matrix.mulVecLin_apply]; exact hz)) hc
    rw [hx0, hc0, add_zero]

end Field

section Semilocal

variable {R : Type*} [CommRing R] {n : ℕ}

def redV (m : Ideal R) (v : Fin (n + 1) → R) : Fin (n + 1) → R ⧸ m := fun i => Ideal.Quotient.mk m (v i)

def Kbar (m : Ideal R) [m.IsMaximal] (K : Submodule R (Fin (n + 1) → R)) :
    letI := Ideal.Quotient.field m; Submodule (R ⧸ m) (Fin (n + 1) → R ⧸ m) :=
  letI := Ideal.Quotient.field m
  { carrier := redV m '' (K : Set (Fin (n + 1) → R))
    add_mem' := by
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, K.add_mem ha hb, by funext i; simp [redV]⟩
    zero_mem' := ⟨0, K.zero_mem, by funext i; simp [redV]⟩
    smul_mem' := by
      rintro c _ ⟨a, ha, rfl⟩
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      exact ⟨c' • a, K.smul_mem c' ha, by funext i; simp [redV]⟩ }

theorem exists_local (m : Ideal R) [hm : m.IsMaximal] (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (K : Submodule R (Fin (n + 1) → R)) (hA : ∀ i, A i (Fin.last n) = if i = Fin.last n then 1 else 0)
    (hK : ∀ v, ∃ x, v - A *ᵥ x ∈ K) :
    ∃ G : Matrix (Fin (n + 1)) (Fin (n + 1)) R, (∀ j, (fun i => G i j) ∈ K) ∧ (∀ i, G i (Fin.last n) = 0) ∧
      (A + G).det ∉ m := by
  classical
  letI := Ideal.Quotient.field m
  let Ab : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⧸ m) := A.map (Ideal.Quotient.mk m)
  have hAb : ∀ i, Ab i (Fin.last n) = if i = Fin.last n then 1 else 0 := by
    intro i
    simp only [Ab, Matrix.map_apply, hA i]
    split_ifs <;> simp
  have hKb : ∀ v, ∃ x, v - Ab *ᵥ x ∈ Kbar m K := by
    intro v
    obtain ⟨w, rfl⟩ : ∃ w : Fin (n + 1) → R, redV m w = v :=
      ⟨fun i => (Ideal.Quotient.mk_surjective (v i)).choose,
        funext fun i => (Ideal.Quotient.mk_surjective (v i)).choose_spec⟩
    obtain ⟨x, hx⟩ := hK w
    refine ⟨redV m x, ?_⟩
    show _ ∈ redV m '' (K : Set (Fin (n + 1) → R))
    refine ⟨w - A *ᵥ x, hx, ?_⟩
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [redV, Ab, Matrix.mulVec, dotProduct, map_sum]
  obtain ⟨Hb, hHcol, hHlast, hdet⟩ := srLift_field Ab (Kbar m K) hAb hKb
  have hlift : ∀ j, ∃ g : Fin (n + 1) → R, g ∈ K ∧ redV m g = fun i => Hb i j := by
    intro j
    obtain ⟨g, hg, hge⟩ := hHcol j
    exact ⟨g, hg, hge⟩
  choose g hgK hgr using hlift
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j => if j = Fin.last n then 0 else g j i
  refine ⟨G, fun j => ?_, fun i => by simp [G], ?_⟩
  · by_cases hj : j = Fin.last n
    · simp only [G, hj, if_true]
      exact K.zero_mem
    · simp only [G, hj, if_false]
      exact hgK j
  · intro hmem
    apply hdet
    have e : Ideal.Quotient.mk m (A + G).det = (Ab + Hb).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
      congr 1
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, map_add (f := _), Ab]
      congr 1
      by_cases hj : j = Fin.last n
      · subst hj
        rw [hHlast i, show G i (Fin.last n) = 0 from if_pos rfl, map_zero]
      · rw [show G i j = g j i from if_neg hj]
        exact congrFun (hgr j) i
    calc (Ab + Hb).det = Ideal.Quotient.mk m (A + G).det := e.symm
      _ = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hmem

theorem exists_idem (S : Finset (Ideal R)) (hS : ∀ m ∈ S, m.IsMaximal) (m : Ideal R) (hm : m ∈ S) :
    ∃ e : R, e - 1 ∈ m ∧ ∀ m' ∈ S, m' ≠ m → e ∈ m' := by
  classical
  have hb : ∀ m' ∈ S, m' ≠ m → ∃ b, b ∈ m' ∧ b - 1 ∈ m := by
    intro m' hm' hne
    have h1 : (1 : R) ∈ m ⊔ m' := by
      rw [Ideal.IsMaximal.coprime_of_ne (hS m hm) (hS m' hm') (Ne.symm hne)]
      exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    refine ⟨b, hb, ?_⟩
    rw [show b - 1 = -a by rw [← hab]; ring]
    exact m.neg_mem ha
  choose! b hbm hb1 using hb
  refine ⟨∏ m' ∈ S.erase m, b m', ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, map_prod, map_one]
    apply Finset.prod_eq_one
    intro m' hm'
    rw [Finset.mem_erase] at hm'
    rw [Ideal.Quotient.eq.2 (hb1 m' hm'.2 hm'.1), map_one]
  · intro m' hm' hne
    rw [← Finset.mul_prod_erase (S.erase m) b (Finset.mem_erase.2 ⟨hne, hm'⟩)]
    exact Ideal.mul_mem_right _ _ (hbm m' hm' hne)

theorem srLift_of_finite (hfin : {m : Ideal R | m.IsMaximal}.Finite) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (K : Submodule R (Fin (n + 1) → R)) (hA : ∀ i, A i (Fin.last n) = if i = Fin.last n then 1 else 0)
    (hK : ∀ v, ∃ x, v - A *ᵥ x ∈ K) :
    ∃ H : Matrix (Fin (n + 1)) (Fin (n + 1)) R, (∀ j, (fun i => H i j) ∈ K) ∧ (∀ i, H i (Fin.last n) = 0) ∧
      IsUnit (A + H).det := by
  classical
  let S := hfin.toFinset
  have hSm : ∀ m ∈ S, m.IsMaximal := fun m hm => hfin.mem_toFinset.1 hm
  have hloc : ∀ m ∈ S, ∃ G : Matrix (Fin (n + 1)) (Fin (n + 1)) R, (∀ j, (fun i => G i j) ∈ K) ∧
      (∀ i, G i (Fin.last n) = 0) ∧ (A + G).det ∉ m := fun m hm => by
    haveI := hSm m hm
    exact exists_local m A K hA hK
  choose! G hGK hGl hGd using hloc
  have hidem : ∀ m ∈ S, ∃ e : R, e - 1 ∈ m ∧ ∀ m' ∈ S, m' ≠ m → e ∈ m' :=
    fun m hm => exists_idem S hSm m hm
  choose! e he1 he0 using hidem
  refine ⟨∑ m ∈ S, e m • G m, fun j => ?_, fun i => ?_, ?_⟩
  · have hc : (fun i => (∑ m ∈ S, e m • G m) i j) = ∑ m ∈ S, e m • fun i => G m i j := by
      funext i
      simp [Matrix.sum_apply, Finset.sum_apply]
    rw [hc]
    exact K.sum_mem fun m hm => K.smul_mem _ (hGK m hm j)
  · rw [Matrix.sum_apply]
    exact Finset.sum_eq_zero fun m hm => by rw [Matrix.smul_apply, hGl m hm i, smul_zero]
  · by_contra hu
    obtain ⟨M, hM, hdetM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
    have hMS : M ∈ S := hfin.mem_toFinset.2 hM
    apply hGd M hMS
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hdetM ⊢
    rw [RingHom.map_det, RingHom.mapMatrix_apply] at hdetM ⊢
    convert hdetM using 2
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add (f := _)]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.sum_apply, map_sum, Finset.sum_eq_single M]
    · have h1 : Ideal.Quotient.mk M (e M) = 1 := by
        rw [← map_one (Ideal.Quotient.mk M)]
        exact Ideal.Quotient.eq.2 (he1 M hMS)
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, h1, one_mul]
    · intro b hb hbM
      rw [Matrix.smul_apply, smul_eq_mul, map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2 (he0 b hb M hMS (Ne.symm hbM)), zero_mul]
    · intro h
      exact absurd hMS h

end Semilocal

end Formalism.L2.SG.Pf.SRL
end
end

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

def RFinMax : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Formalism.MainNotions.S.Loc.Model F E), M.OK → {m : Ideal M.R | m.IsMaximal}.Finite

theorem srLift_of_finMax (h : RFinMax) : SRLift := by
  intro F _ _ _ E _ _ _ _ M hOK n A K hA hK
  exact Formalism.L2.SG.Pf.SRL.srLift_of_finite (h M hOK) A K hA hK

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end

noncomputable section

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents.RF

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG ValuativeRel PI.IntegralDiscriminantMembership

theorem finite_max_of {R : Type*} [CommRing R] (c : R) (hc : ∀ m : Ideal R, m.IsMaximal → c ∈ m)
    (hfin : Finite (R ⧸ Ideal.span {c})) : {m : Ideal R | m.IsMaximal}.Finite := by
  haveI := hfin
  haveI : Finite (Ideal (R ⧸ Ideal.span {c})) :=
    Finite.of_injective (fun I : Ideal (R ⧸ Ideal.span {c}) => (I : Set (R ⧸ Ideal.span {c}))) SetLike.coe_injective
  refine (Set.finite_univ.image (fun J : Ideal (R ⧸ Ideal.span {c}) => Ideal.comap (Ideal.Quotient.mk _) J)).subset ?_
  intro m hm
  refine ⟨Ideal.map (Ideal.Quotient.mk _) m, Set.mem_univ _, ?_⟩
  dsimp only
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem m).mpr (hc m hm))

theorem finite_max_of_equiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : {m : Ideal S | m.IsMaximal}.Finite) : {m : Ideal R | m.IsMaximal}.Finite := by
  refine (h.image (fun n : Ideal S => Ideal.comap e n)).subset ?_
  intro m hm
  haveI : m.IsMaximal := hm
  refine ⟨Ideal.map e m, Ideal.map_isMaximal_of_equiv e, ?_⟩
  first
  | exact Ideal.comap_map_of_bijective _ e.bijective
  | exact Ideal.comap_map_of_bijective e e.bijective
  | simp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem unit_one_sub (M : Model F E) (hOK : M.OK) (π : 𝒪[F]) (hπ : π ∈ nonunits 𝒪[F]) (r : M.L.O) :
    IsUnit (1 - (⟨algebraMap F E (π : F), (alg_mem_O M).mpr π.2⟩ : M.L.O) * r) := by
  have := hOK.loc
  haveI : IsLocalRing 𝒪[F] := inferInstance
  obtain ⟨⟨tr, htr⟩, ⟨nr, hnr⟩⟩ := (mem_O_iff M r).mp r.2
  set x : E := 1 - algebraMap F E (π : F) * r with hx
  have hcj : M.L.cj x = 1 - algebraMap F E (π : F) * M.L.cj r := by
    rw [hx, map_sub, map_one, map_mul, cj_alg]
  have hN : x * M.L.cj x = algebraMap F E ((1 : F) - (π : F) * ((tr : F) - (π : F) * (nr : F))) := by
    rw [hcj, hx]
    simp only [map_sub, map_one, map_mul]
    rw [htr, hnr]; ring
  set n : 𝒪[F] := 1 - π * (tr - π * nr) with hn
  have hnu : IsUnit n := by
    apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
    exact mul_mem_nonunits_left hπ
  obtain ⟨nu, hnu'⟩ := hnu
  have hNn : x * M.L.cj x = algebraMap F E (n : F) := by rw [hN, hn]; push_cast; ring_nf
  have hyO : M.L.cj x * algebraMap F E ((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) ∈ M.L.O :=
    M.L.O.mul_mem (Formalism.L2.SG.Pf.Cnt.DualityBasisChange.cj_mem_O (M := M) x (by
      rw [hx]; exact M.L.O.sub_mem M.L.O.one_mem (M.L.O.mul_mem ((alg_mem_O M).mpr π.2) r.2)))
      ((alg_mem_O M).mpr (nu⁻¹ : 𝒪[F]ˣ).1.2)
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hyO⟩, Subtype.ext ?_⟩
  show x * (M.L.cj x * algebraMap F E ((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) = 1
  rw [← mul_assoc, hNn, ← map_mul, ← hnu']
  rw [show ((nu : 𝒪[F]) : F) * (((nu⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1 by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl, map_one]

theorem finite_max_O (M : Model F E) (hOK : M.OK) : {m : Ideal M.L.O | m.IsMaximal}.Finite := by
  have := hOK.loc
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  set c : M.L.O := ⟨algebraMap F E (π : F), (alg_mem_O M).mpr π.2⟩ with hc
  refine finite_max_of c (fun m hm => ?_) ?_
  · by_contra hcm
    have htop : m ⊔ Ideal.span {c} = ⊤ := hm.1.2 _ (lt_of_le_of_ne le_sup_left (fun h => hcm (h ▸
      Ideal.mem_sup_right (Ideal.mem_span_singleton_self c))))
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : M.L.O) ∈ m ⊔ Ideal.span {c})
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    have hu := unit_one_sub M hOK π hπ.not_isUnit r
    have : a = 1 - c * r := by rw [← hab]; ring
    rw [this] at ha
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
  · have h := card_quot_pi M hOK π hπ
    have hq : 0 < qF F := Nat.card_pos (α := 𝓀[F])
    exact Nat.finite_of_card_ne_zero (by rw [h]; positivity)

section ModeG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem mem_R_some (M : Model F E) {g : SplitG M.L} (hs : M.split = some g) (x : E) :
    x ∈ M.R ↔ ∃ a b : 𝒪[F], g.e x = ((a : F), (b : F)) ∧
      Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b := by
  unfold Formalism.MainNotions.S.Loc.Model.R
  rw [hs]
  simp only [Subring.mem_comap, Subring.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hab, he⟩
    exact ⟨a, b, he.symm, hab⟩
  · rintro ⟨a, b, he, hab⟩
    exact ⟨(a, b), hab, he.symm⟩

theorem isUnit_of_fst (M : Model F E) (hOK : M.OK) {g : SplitG M.L} (hs : M.split = some g) (x : M.R)
    (a b : 𝒪[F]) (he : g.e x = ((a : F), (b : F)))
    (hab : Ideal.Quotient.mk (Ideal.span {g.q}) a = Ideal.Quotient.mk (Ideal.span {g.q}) b) (ha : IsUnit a) :
    IsUnit x := by
  have := hOK.loc
  haveI : IsLocalRing 𝒪[F] := inferInstance
  obtain ⟨s, hsq⟩ := Ideal.mem_span_singleton'.1 ((Ideal.Quotient.eq).1 hab.symm)
  have hqn : g.q ∈ nonunits 𝒪[F] := g.q_irr.not_isUnit
  have hqm : g.q ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal _).2 hqn
  have hb : IsUnit b := by
    by_contra hb
    have hbm : b ∈ IsLocalRing.maximalIdeal 𝒪[F] := (IsLocalRing.mem_maximalIdeal _).2 hb
    have ham : a ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
      have : a = b - s * g.q := by rw [hsq]; ring
      rw [this]
      exact Ideal.sub_mem _ hbm (Ideal.mul_mem_left _ _ hqm)
    exact (IsLocalRing.mem_maximalIdeal _).1 ham ha
  obtain ⟨ua, rfl⟩ := ha
  obtain ⟨ub, rfl⟩ := hb
  set y : E := g.e.symm (((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]), ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) with hy
  have hyR : y ∈ M.R := by
    rw [mem_R_some M hs]
    refine ⟨_, _, by rw [hy, AlgEquiv.apply_symm_apply], ?_⟩
    rw [Ideal.Quotient.eq]
    refine Ideal.mem_span_singleton'.2 ⟨((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * s, ?_⟩
    have h1 : ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (ub : 𝒪[F]) = 1 := Units.inv_mul ub
    have h2 : ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (ua : 𝒪[F]) = 1 := Units.inv_mul ua
    have e1 : ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) - ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) =
        ((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * ((ub : 𝒪[F]) - (ua : 𝒪[F])) := by
      linear_combination (-((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F])) * h1 + ((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * h2
    rw [e1, ← hsq]; ring
  refine isUnit_iff_exists_inv.2 ⟨⟨y, hyR⟩, Subtype.ext ?_⟩
  show (x : E) * y = 1
  apply g.e.injective
  rw [map_mul, he, hy, AlgEquiv.apply_symm_apply, map_one]
  ext
  · show ((ua : 𝒪[F]) : F) * (((ua⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  · show ((ub : 𝒪[F]) : F) * (((ub⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) = 1
    rw [← Subring.coe_mul, Units.mul_inv]; rfl

theorem fst_isUnit (M : Model F E) {g : SplitG M.L} (hs : M.split = some g) (x : M.R) (hx : IsUnit x)
    (a b : 𝒪[F]) (he : g.e x = ((a : F), (b : F))) : IsUnit a := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨a', b', he', -⟩ := (mem_R_some M hs (((u⁻¹ : (M.R)ˣ) : M.R) : E)).mp ((u⁻¹ : (M.R)ˣ) : M.R).2
  have h1 : g.e ((((u : (M.R)ˣ) : M.R) : E) * (((u⁻¹ : (M.R)ˣ) : M.R) : E)) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one, map_one]
  rw [map_mul, he, he'] at h1
  have h2 : (a : F) * a' = 1 := congrArg Prod.fst h1
  exact ⟨⟨a, a', Subtype.ext (by push_cast; exact h2), Subtype.ext (by push_cast; rw [mul_comm]; exact h2)⟩, rfl⟩

theorem isLocal_R (M : Model F E) (hOK : M.OK) {g : SplitG M.L} (hs : M.split = some g) : IsLocalRing M.R := by
  have := hOK.loc
  haveI : IsLocalRing 𝒪[F] := inferInstance
  haveI : Nontrivial M.R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 := congrArg (fun x : M.R => (g.e (x : E)).1) h
    simp at h1
  refine IsLocalRing.of_nonunits_add fun x y hx hy hxy => ?_
  obtain ⟨a, b, he, hab⟩ := (mem_R_some M hs x).1 x.2
  obtain ⟨a', b', he', hab'⟩ := (mem_R_some M hs y).1 y.2
  have hsum : g.e ((x + y : M.R) : E) = (((a + a' : 𝒪[F]) : F), ((b + b' : 𝒪[F]) : F)) := by
    rw [Subring.coe_add, map_add (f := _), he, he']; simp
  have hu := fst_isUnit M hs (x + y) hxy (a + a') (b + b') hsum
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
  · exact hx (isUnit_of_fst M hOK hs x a b he hab h)
  · exact hy (isUnit_of_fst M hOK hs y a' b' he' hab' h)

end ModeG

theorem rFinMax_holds : RFinMax := by
  intro F _ _ _ E _ _ _ _ M hOK
  cases hs : M.split with
  | none =>
    exact finite_max_of_equiv (RingEquiv.subringCongr (PI.NGStepBBW.R_eq_O_of_none hs)) (finite_max_O M hOK)
  | some g =>
    haveI := isLocal_R M hOK hs
    refine (Set.finite_singleton (IsLocalRing.maximalIdeal M.R)).subset ?_
    intro m hm
    exact IsLocalRing.eq_maximalIdeal hm

theorem srLift_holds : SRLift := srLift_of_finMax rFinMax_holds

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents.RF
end
end

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

open Formalism.MainNotions.S.LocalSplitGroups

theorem LiftOrb_holds : LiftOrb := liftOrb_of RF.srLift_holds

theorem GaPlusTh_holds {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) : GaPlusTh M δ u u' :=
  gaPlusTh_of LiftOrb_holds M δ u u'

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
