module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfCoefficients
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfInputs
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Th21
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameZEqLinZu
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UUEEqAsp
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.OmpCoset
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FvecMapFlag
noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem omp_congr {F G : FlagG S r T} {F' G' : FlagG S r T'} (h : ∀ a, F.fvec a = G.fvec a)
    (h' : ∀ a, F'.fvec a = G'.fvec a) : omp F F' = omp G G' ∧ Zhat F F' = Zhat G G' := by
  have hF : F.fvec = G.fvec := funext h
  have hF' : F'.fvec = G'.fvec := funext h'
  have hZ : Zhat F F' = Zhat G G' := by
    unfold Zhat
    first
      | rw [hF, hF']
      | (simp only [hF, hF']; rfl)
  refine ⟨?_, hZ⟩
  unfold omp
  rw [hZ, hF']

theorem fvec_mapFlag (g : S.V ≃ₗ[E] S.V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (b : Fin (r + 1)) :
    (mapFlag g hg F).fvec b = g (F.fvec b) := by
  unfold FlagG.fvec
  induction b using Fin.lastCases with
  | last => simp [mapFlag]
  | cast i => simp [mapFlag]

theorem coef_mat (F : FlagG S r T) (s : S.V →ₗ[E] S.V) (hs : ∀ j, ∀ x ∈ F.Xa (j + 1), s x - x ∈ F.Xa j)
    (hz : s F.z - F.z ∈ F.X) :
    ∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c) ∧ M.det = 1 ∧
      ∀ c, M (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  have hcolE : ∀ b' : Fin r, ∃ l : Fin r →₀ E, (∀ i : Fin r, ¬ i.1 < b'.1 → l i = 0) ∧
      s (F.e b') = F.e b' + ∑ i, l i • F.e i := by
    intro b'
    have hmem : F.e b' ∈ F.Xa (b'.1 + 1) := Submodule.subset_span ⟨b', Nat.lt_succ_self _, rfl⟩
    have h1 := hs b'.1 (F.e b') hmem
    obtain ⟨l, hl, hl2⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 h1
    refine ⟨l, fun i hi => (Finsupp.mem_supported' E l).1 hl i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hl2
    rw [hl2]
    abel
  choose l hl0 hl using hcolE
  obtain ⟨cz, hcz⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hz
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun c b =>
    Fin.lastCases (motive := fun _ => E)
      (Fin.lastCases (motive := fun _ => E) 1 (fun i => cz i) c)
      (fun b' => Fin.lastCases (motive := fun _ => E) 0 (fun i => (if i = b' then 1 else 0) + l b' i) c) b
  have hMcol : ∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, one_smul]
      have h2 : s F.z = F.z + ∑ i, cz i • F.e i := by
        rw [hcz]
        abel
      rw [h2, add_comm]
    | cast b' =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, zero_smul, add_zero, add_smul, Finset.sum_add_distrib, ite_smul,
        one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hl b'
  have hdiag : ∀ i, M i i = 1 := by
    intro i
    induction i using Fin.lastCases with
    | last => simp [M]
    | cast i => simp [M, hl0 i i (lt_irrefl _)]
  have htri : M.BlockTriangular id := by
    intro i j hij
    induction j using Fin.lastCases with
    | last => exact absurd hij (not_lt.2 (Fin.le_last i))
    | cast j =>
      induction i using Fin.lastCases with
      | last => simp [M]
      | cast i =>
        have hji : j < i := by simpa using hij
        have hne : i ≠ j := (ne_of_lt hji).symm
        simp [M, hne, hl0 j i (not_lt.2 (le_of_lt hji))]
  refine ⟨M, hMcol, ?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  · intro c
    induction c using Fin.lastCases with
    | last => simp [M]
    | cast c => simp [M, Fin.castSucc_ne_last]

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

private theorem adjugate_last_col_sum_and_det_of_coset (Z Z' P Q : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (v v' : Fin (r + 1) → S.V) (φ : S.V →ₗ[E] S.V) (hZ : Z' = P * Z * Q)
    (hv : ∀ b, v' b = φ (∑ c, Q c b • v c)) (hQ : Q.det = 1) (hP : P.det = 1)
    (hPl : ∀ a, P a (Fin.last r) = if a = Fin.last r then 1 else 0) :
    ∑ b, Z'.adjugate b (Fin.last r) • v' b = φ (∑ b, Z.adjugate b (Fin.last r) • v b) ∧
      Z'.det = Z.det := by
  have hQQ : Q * Q.adjugate = 1 := by rw [Matrix.mul_adjugate, hQ, one_smul]
  have hPP : P.adjugate * P = 1 := by rw [Matrix.adjugate_mul, hP, one_smul]
  have hPl' : ∀ d, P.adjugate d (Fin.last r) = if d = Fin.last r then 1 else 0 := by
    intro d
    have := congrFun (congrFun hPP d) (Fin.last r)
    simpa [Matrix.mul_apply, hPl, Matrix.one_apply] using this
  have hW : ∀ c, (Q * (Q.adjugate * (Z.adjugate * P.adjugate))) c (Fin.last r) =
      Z.adjugate c (Fin.last r) := by
    intro c
    rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul, Matrix.mul_apply]
    simp [hPl']
  refine ⟨?_, ?_⟩
  · rw [hZ, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hv, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, ← hW c, Matrix.mul_apply]
    congr 1
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  · rw [hZ, Matrix.det_mul, Matrix.det_mul, hP, hQ, one_mul, mul_one]

theorem omp_coset (F : FlagG S r T) (F0 : FlagG S r T') (σ γ1 s' : S.V ≃ₗ[E] S.V)
    (hσ : σ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hσ' : σ.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hγ1 : γ1 ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hγ2 : σ * γ1 * s' ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hσf : ∀ j, ∀ x ∈ F.Xa (j + 1), σ.symm x - x ∈ F.Xa j) (hσz : σ.symm F.z - F.z ∈ F.X)
    (hsf : ∀ j, ∀ x ∈ F0.Xa (j + 1), s' x - x ∈ F0.Xa j) (hsz : s' F0.z - F0.z ∈ F0.X) :
    omp F (mapFlag (σ * γ1 * s') hγ2 F0) = σ (omp F (mapFlag γ1 hγ1 F0)) ∧
    (Zhat F (mapFlag (σ * γ1 * s') hγ2 F0)).det = (Zhat F (mapFlag γ1 hγ1 F0)).det ∧
    omp (mapFlag (σ * γ1 * s') hγ2 F0) F = σ (omp (mapFlag γ1 hγ1 F0) F) ∧
    (Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F).det = (Zhat (mapFlag γ1 hγ1 F0) F).det := by
  obtain ⟨M, hM, hMd, hMl⟩ := coef_mat F0 (s' : S.V →ₗ[E] S.V) (fun j x hx => hsf j x hx) hsz
  obtain ⟨N, hN, hNd, hNl⟩ := coef_mat F (σ.symm : S.V →ₗ[E] S.V) (fun j x hx => hσf j x hx) hσz
  have hM' : ∀ b, s' (F0.fvec b) = ∑ c, M c b • F0.fvec c := hM
  have hN' : ∀ b, σ.symm (F.fvec b) = ∑ c, N c b • F.fvec c := hN
  have hs : ∀ x y, S.hT (σ x) (σ y) = S.hT x y := hσ
  have hv1 : ∀ b, (mapFlag (σ * γ1 * s') hγ2 F0).fvec b =
      σ (∑ c, M c b • (mapFlag γ1 hγ1 F0).fvec c) := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [fvec_mapFlag, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hM' b, map_sum]
    simp only [fvec_mapFlag, map_smul]
  have hv2 : ∀ b, F.fvec b = σ (∑ c, N c b • F.fvec c) := by
    intro b
    rw [← hN', LinearEquiv.apply_symm_apply]
  have hZ1 : Zhat F (mapFlag (σ * γ1 * s') hγ2 F0) = Nᴴ * Zhat F (mapFlag γ1 hγ1 F0) * M := by
    ext a b
    have e1 : Zhat F (mapFlag (σ * γ1 * s') hγ2 F0) a b =
        S.hT (F.fvec a) ((mapFlag (σ * γ1 * s') hγ2 F0).fvec b) := rfl
    rw [e1, hv1 b, hv2 a, hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Zhat, brS, starRingEnd_apply,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hZ2 : Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F = Mᴴ * Zhat (mapFlag γ1 hγ1 F0) F * N := by
    ext a b
    have e1 : Zhat (mapFlag (σ * γ1 * s') hγ2 F0) F a b =
        S.hT ((mapFlag (σ * γ1 * s') hγ2 F0).fvec a) (F.fvec b) := rfl
    rw [e1, hv1 a, hv2 b, hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
      smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply, Zhat, brS, starRingEnd_apply,
      Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨h1, h2⟩ := adjugate_last_col_sum_and_det_of_coset _ _ _ _ _ _ (σ : S.V →ₗ[E] S.V) hZ1 hv1 hMd
    (by simp [Matrix.det_conjTranspose, hNd])
    (by intro a; rw [Matrix.conjTranspose_apply, hNl]; split_ifs <;> simp)
  obtain ⟨h3, h4⟩ := adjugate_last_col_sum_and_det_of_coset _ _ _ _ _ _ (σ : S.V →ₗ[E] S.V) hZ2 hv2 hNd
    (by simp [Matrix.det_conjTranspose, hMd])
    (by intro a; rw [Matrix.conjTranspose_apply, hMl]; split_ifs <;> simp)
  exact ⟨h1, h2, h3, h4⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UUE_eq_Asp {D : D7} {T T' : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : Submodule.IsFullLattice D.host.E Λ) (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (hL : IsLift Λ F) (hL' : IsLift Λ F') : UUE Λ F F' = Asp F.fl F'.fl := by
  refine le_antisymm ?_ ?_
  · have hX' : F'.fl.X ≤ Asp F.fl F'.fl := by rw [← Asp_symm]; exact X_le_Asp F'.fl F.fl
    have hz' : F'.fl.z ∈ Asp F.fl F'.fl := by rw [← Asp_symm]; exact z_mem_Asp F'.fl F.fl
    have key : UU Λ F F' ≤ (Asp F.fl F'.fl).restrictScalars (𝓞 D.host.E) := by
      unfold UU
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro y hy
        exact X_le_Asp F.fl F'.fl (Submodule.mem_inf.1 hy).2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL.2]
        exact z_mem_Asp F.fl F'.fl
      · intro y hy
        exact hX' (Submodule.mem_inf.1 hy).2
      · rw [Submodule.span_le, Set.singleton_subset_iff, hL'.2]
        exact hz'
    unfold UUE spanE
    rw [Submodule.span_le]
    intro x hx
    exact key hx
  · rw [Asp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact PI.PairCorankPos.W.frame_mem_UUE Λ hΛ F F' hL hL' i

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 800000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem frame_fvec (t : TauC Y u u') (b : Fin (D.R.rS + 1)) : t.frame.fl.fvec b = t.lin ((X.Fu u').fvec b) := by
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  show (mapLF t.lin (lf D (X.Fu u'))).fl.fvec b = _
  rw [mapLF_fl hγ, fvec_mapFlag]

theorem frame_z_eq_lin_zu (t : TauC Y u u') : t.frame.fl.z = t.lin (X.Fu u').z := by
  have := frame_fvec Y t (Fin.last _)
  simpa [FlagG.fvec, Fin.snoc_last] using this

theorem mem_frameX (t : TauC Y u u') (x : (VS D).V) : x ∈ t.frame.fl.X ↔ t.lin.symm x ∈ (X.Fu u').X :=
  CorankRelation.mem_Xsp_mapLF t.lin t.rep.2.2.1 (lf D (X.Fu u')) x

theorem omp_terms (t1 t2 : TauC Y u u') (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u'))) (he : t2.lin = σ * t1.lin * s') :
    omp (X.Fu u) t2.frame.fl = σ (omp (X.Fu u) t1.frame.fl) ∧
    Dl (X.Fu u) t2.frame.fl (D.R.rS + 1) = Dl (X.Fu u) t1.frame.fl (D.R.rS + 1) ∧
    omp t2.frame.fl (X.Fu u) = σ (omp t1.frame.fl (X.Fu u)) ∧
    Dl t2.frame.fl (X.Fu u) (D.R.rS + 1) = Dl t1.frame.fl (X.Fu u) (D.R.rS + 1) := by
  have hσ' := SRat_inv (lf D (X.Fu u)) hσ
  obtain ⟨hσi, -, -⟩ := hσ
  obtain ⟨hσi', hσf', hσz'⟩ := hσ'
  obtain ⟨-, hsf, hsz⟩ := hs'
  have hγ1 : t1.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t1.rep.2.2.1
  have hγ2 : σ * t1.lin * s' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := he ▸ t2.rep.2.2.1
  obtain ⟨o1, o2, o3, o4⟩ := omp_coset (X.Fu u) (X.Fu u') σ t1.lin s' hσi hσi' hγ1 hγ2 hσf' hσz' hsf hsz
  have hF1 : t1.frame.fl = mapFlag t1.lin hγ1 (X.Fu u') := mapLF_fl hγ1 (lf D (X.Fu u'))
  have hF2 : ∀ b, t2.frame.fl.fvec b = (mapFlag (σ * t1.lin * s') hγ2 (X.Fu u')).fvec b := fun b => by
    rw [frame_fvec, fvec_mapFlag, he]
  have hrefl : ∀ b, (X.Fu u).fvec b = (X.Fu u).fvec b := fun b => rfl
  obtain ⟨k1, k2⟩ := omp_congr (F := X.Fu u) (G := X.Fu u) hrefl hF2
  obtain ⟨k3, k4⟩ := omp_congr (F := t2.frame.fl) (G := mapFlag (σ * t1.lin * s') hγ2 (X.Fu u')) hF2 hrefl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact k1.trans (o1.trans (congrArg (fun G => σ (omp (X.Fu u) G)) hF1.symm))
  · refine ((det_eq_Dl _ _).symm.trans ?_).trans (det_eq_Dl _ _)
    exact (congrArg Matrix.det k2).trans (o2.trans (congrArg (fun G => (Zhat (X.Fu u) G).det) hF1.symm))
  · exact k3.trans (o3.trans (congrArg (fun G => σ (omp G (X.Fu u))) hF1.symm))
  · refine ((det_eq_Dl _ _).symm.trans ?_).trans (det_eq_Dl _ _)
    exact (congrArg Matrix.det k4).trans (o4.trans (congrArg (fun G => (Zhat G (X.Fu u)).det) hF1.symm))

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem th21 (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0) (h2 : Gt t2 ≠ 0)
    (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) :
    t1.lam = t0.lam ∧ t2.lam = t0.lam ∧
    Th t0.lam (lf D (X.Fu u)) t2.frame t1.frame (t1.lin * t2.lin⁻¹) = Hp t0.lam (lf D (X.Fu u)) t2.frame := by
  have hdim := Formalism.L2.SG.Corank.finrank_VS D
  obtain ⟨hrow1, hs01⟩ := hR1
  obtain ⟨hrow2, hs02⟩ := hR2
  have hl1 : t1.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow1
  have hl1' : t1.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow1
  have hl2 : t2.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow2
  have hl2' : t2.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow2
  have hlat : Submodule.IsFullLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).1.1
  have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
  have hL0 : IsLift t0.lam t0.frame := t0.rep.2.2.2.2.1
  have hL1 : IsLift t0.lam t1.frame := by rw [← hl1]; exact t1.rep.2.2.2.2.1
  have hL2 : IsLift t0.lam t2.frame := by rw [← hl2]; exact t2.rep.2.2.2.2.1
  have hG0 := G_ne_of_Gt Y h0
  have hG1 := G_ne_of_Gt Y h1
  have hG2 := G_ne_of_Gt Y h2
  have hTh1 : Th t0.lam (lf D (X.Fu u)) t0.frame t1.frame (t1.lin * t0.lin⁻¹) = Hp t0.lam (lf D (X.Fu u)) t0.frame := by
    have h : Formalism.L2.SG.TermOp.s0T t0 t1 = 1 := hs01
    unfold Formalism.L2.SG.TermOp.s0T at h
    rw [if_pos ⟨hl1.symm, hl1'.symm⟩] at h
    exact (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam hlat _ t0.frame t1.frame _ hLF hL0 hG0).1 h
  have hTh2 : Th t0.lam (lf D (X.Fu u)) t0.frame t2.frame (t2.lin * t0.lin⁻¹) = Hp t0.lam (lf D (X.Fu u)) t0.frame := by
    have h : Formalism.L2.SG.TermOp.s0T t0 t2 = 1 := hs02
    unfold Formalism.L2.SG.TermOp.s0T at h
    rw [if_pos ⟨hl2.symm, hl2'.symm⟩] at h
    exact (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam hlat _ t0.frame t2.frame _ hLF hL0 hG0).1 h
  have hsym1 := CorankRelation.Th_symm D.R.k hdim t0.lam hlat _ t0.frame t1.frame (t1.lin * t0.lin⁻¹) hLF hL0 hL1 hG0 hG1
    (CorankRelation.frame_mem_iff t0 t1) hTh1
  rw [show (t1.lin * t0.lin⁻¹)⁻¹ = t0.lin * t1.lin⁻¹ by group] at hsym1
  have htr := CorankRelation.Th_trans t0.lam _ t1.frame t0.frame t2.frame (t0.lin * t1.lin⁻¹) (t2.lin * t0.lin⁻¹)
    (fun x hx => (CorankRelation.frame_mem_iff t0 t2 x).1 hx) hsym1 hTh2
  rw [show (t2.lin * t0.lin⁻¹) * (t0.lin * t1.lin⁻¹) = t2.lin * t1.lin⁻¹ by group] at htr
  have hsym2 := CorankRelation.Th_symm D.R.k hdim t0.lam hlat _ t1.frame t2.frame (t2.lin * t1.lin⁻¹) hLF hL1 hL2 hG1 hG2
    (CorankRelation.frame_mem_iff t1 t2) htr
  rw [show (t2.lin * t1.lin⁻¹)⁻¹ = t1.lin * t2.lin⁻¹ by group] at hsym2
  exact ⟨hl1, hl2, hsym2⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false
set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem Hp_eq_Hsp (t : TauC Y u u') (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hL : IsLift Λ (lf D (X.Fu u))) (hL' : IsLift Λ t.frame) :
    Hp Λ (lf D (X.Fu u)) t.frame = Hsp (X.Fu u) t.frame.fl := by
  unfold Hp Hsp
  rw [UUE_eq_Asp Λ (by first | exact hΛ | exact hΛ.toIsLattice) _ _ hL hL']

theorem lemmaG3_of_inputs (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0)
    (h2 : Gt t2 ≠ 0) (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) (hG1 : t1.G = t0.G) (hG2 : t2.G = t0.G)
    (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u')))
    (he : t2.lin = σ * t1.lin * s') (ha : coefA Y u u' t0 t1 = coefA Y u u' t0 t2)
    (ha' : coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2) :
    σ (omp (X.Fu u) t1.frame.fl) - omp (X.Fu u) t1.frame.fl ∈ (X.Fu u).X ∧
    (t1.lin * s'⁻¹ * t1.lin⁻¹) (omp t1.frame.fl (X.Fu u)) - omp t1.frame.fl (X.Fu u) ∈ t1.frame.fl.X ∧
    ∀ w ∈ Hsp (X.Fu u) t1.frame.fl, ∃ w0 ∈ Hsp (X.Fu u) t1.frame.fl,
      σ w - w0 ∈ (X.Fu u).X ∧ (t1.lin * s'⁻¹ * t1.lin⁻¹) w - w0 ∈ t1.frame.fl.X := by
  have line_occ (t0 t : TauC Y u u') (h0 : Gt t0 ≠ 0) (h : Gt t ≠ 0) (hR : RelC Y u u' t0 t) (hG : t.G = t0.G)
      (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') :
      (yT Y u u' t - coefA Y u u' t0 t • yT Y u u' t0 ∈ (X.Fu u).X ∧
        coefA Y u u' t0 t * star (coefA Y u u' t0 t) = 1) ∧
      (yT' Y u u' t - coefA' Y u u' t0 t • yT' Y u u' t0 ∈ (X.Fu u').X ∧
        coefA' Y u u' t0 t * star (coefA' Y u u' t0 t) = 1) := by
    have hdim := Formalism.L2.SG.Corank.finrank_VS D
    obtain ⟨hrow, hs0⟩ := hR
    have hlam : t.lam = t0.lam := congrArg (fun r => (r.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow
    have hlam' : t.lam' = t0.lam' := congrArg (fun r => (r.2.1 : Submodule (𝓞 D.host.E) (VS D).V)) hrow
    have hlat : Submodule.IsFullLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).1.1
    have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
    have hL1 : IsLift t0.lam t0.frame := t0.rep.2.2.2.2.1
    have hL2 : IsLift t0.lam t.frame := by rw [← hlam]; exact t.rep.2.2.2.2.1
    have hG1 : Gval (lf D (X.Fu u)) t0.frame ≠ 0 := by
      intro hG
      apply h0
      simp only [Formalism.L2.SG.TermOp.Gt]
      rw [if_pos]
      exact (Formalism.L2.SG.TermDef.Gt_mk (PI.TermAttrConst.UnitaryGroupMassFormula.gFun_all _ _ _) _).trans hG
    have hG12 : Gval (lf D (X.Fu u)) t.frame = Gval (lf D (X.Fu u)) t0.frame := by
      rw [← Formalism.L2.SG.Pf.SatGram.gterm_G Y t, ← Formalism.L2.SG.Pf.SatGram.gterm_G Y t0, hG]
    have hs0' : Lat.s0 t0.lam (lf D (X.Fu u)) t0.frame t.frame (t.lin * t0.lin⁻¹) D.R.k = 1 := by
      have h1 : Formalism.L2.SG.TermOp.s0T t0 t = 1 := hs0
      unfold Formalism.L2.SG.TermOp.s0T at h1
      rw [if_pos ⟨hlam.symm, hlam'.symm⟩] at h1
      exact h1
    have hTh := (CorankRelation.s0_eq_one_iff_Th_eq_Hp D.R.k hdim t0.lam
      (by first | exact hlat | exact hlat.toIsLattice) _ t0.frame t.frame _ hLF hL1 hG1).1 hs0'
    have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hTs : star ((Tu D u : ℕ) : D.host.E) = ((Tu D u : ℕ) : D.host.E) := star_natCast _
    have hTs' : star ((Tu D u' : ℕ) : D.host.E) = ((Tu D u' : ℕ) : D.host.E) := star_natCast _
    refine ⟨line_pair D.R.k hdim t0.lam (by first | exact hlat | exact hlat.toIsLattice) (lf D (X.Fu u)) t0.frame t.frame _ hLF hL1 hL2 hG1 hG12 hTE hTs hTh,
      line_pair' D.R.k hdim t0.lam (by first | exact hlat | exact hlat.toIsLattice) (lf D (X.Fu u)) (lf D (X.Fu u')) t0.lin t.lin t0.rep.2.2.1 t.rep.2.2.1 hLF
        hL1 hL2 hG1 hG12 hTE' hTs' hTh⟩
  obtain ⟨⟨l1, -⟩, ⟨l1', -⟩⟩ := line_occ t0 t1 h0 h1 hR1 hG1 hT hT'
  obtain ⟨⟨l2, -⟩, ⟨l2', -⟩⟩ := line_occ t0 t2 h0 h2 hR2 hG2 hT hT'
  have hy : yT Y u u' t2 - yT Y u u' t1 ∈ (X.Fu u).X := by
    have := Submodule.sub_mem _ l2 l1
    rw [← ha] at this
    convert this using 1
    abel
  have hy' : yT' Y u u' t2 - yT' Y u u' t1 ∈ (X.Fu u').X := by
    have := Submodule.sub_mem _ l2' l1'
    rw [← ha'] at this
    convert this using 1
    abel
  obtain ⟨o1, o2, o3, o4⟩ := omp_terms Y t1 t2 σ s' hσ hs' he
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hs'i := SRat_inv (lf D (X.Fu u')) hs'
  have hσm := hσ
  obtain ⟨hσi, hσf, hσz⟩ := hσm
  obtain ⟨hsi', hsf', hsz'⟩ := hs'i
  have hsymm : ∀ v, t2.lin.symm (σ v) = s'.symm (t1.lin.symm v) := by
    intro v
    apply t2.lin.injective
    rw [LinearEquiv.apply_symm_apply, he]
    show σ v = σ (t1.lin (s' (s'.symm (t1.lin.symm v))))
    simp
  refine ⟨?_, ?_, ?_⟩
  · have e : yT Y u u' t2 - yT Y u u' t1 =
        ((Tu D u : ℕ) : D.host.E) • (σ (omp (X.Fu u) t1.frame.fl) - omp (X.Fu u) t1.frame.fl) := by
      simp only [yT, yv, o1, o2, smul_sub]
      abel
    rw [e] at hy
    exact (Submodule.smul_mem_iff _ hTE).1 hy
  · set ω := omp t1.frame.fl (X.Fu u) with hω
    have e : yT' Y u u' t2 - yT' Y u u' t1 =
        ((Tu D u' : ℕ) : D.host.E) • (s'.symm (t1.lin.symm ω) - t1.lin.symm ω) := by
      simp only [yT', yv, o3, o4, frame_z_eq_lin_zu, map_add (f := _), map_smul, LinearEquiv.symm_apply_apply, hsymm, smul_sub]
      abel
    rw [e] at hy'
    have hv := (Submodule.smul_mem_iff _ hTE').1 hy'
    refine (mem_frameX Y t1 _).2 ?_
    convert hv using 1
    rw [map_sub]
    show t1.lin.symm (t1.lin (s'.symm (t1.lin.symm ω))) - t1.lin.symm ω = _
    rw [LinearEquiv.symm_apply_apply]
  · obtain ⟨hl1, hl2, hTh⟩ := th21 Y t0 t1 t2 h0 h1 h2 hR1 hR2
    have hlat : Submodule.IsFullLattice D.host.E t0.lam := ((Y.rowsOK u).1 t0.lam t0.mem).1.1
    have hLF : IsLift t0.lam (lf D (X.Fu u)) := ((Y.rowsOK u).1 t0.lam t0.mem).2.1.2.2.1
    have hL1 : IsLift t0.lam t1.frame := by rw [← hl1]; exact t1.rep.2.2.2.2.1
    have hL2 : IsLift t0.lam t2.frame := by rw [← hl2]; exact t2.rep.2.2.2.2.1
    have hH1 := Hp_eq_Hsp Y t1 t0.lam hlat hLF hL1
    have hH2 := Hp_eq_Hsp Y t2 t0.lam hlat hLF hL2

    have hX1A : t1.frame.fl.X ≤ Asp (X.Fu u) t1.frame.fl := by
      rw [← Asp_symm]; exact X_le_Asp _ _
    have hz1A : t1.frame.fl.z ∈ Asp (X.Fu u) t1.frame.fl := by
      rw [← Asp_symm]; exact z_mem_Asp _ _
    have hAsp : Asp (X.Fu u) t2.frame.fl ≤ (Asp (X.Fu u) t1.frame.fl).map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [Asp, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      cases i with
      | inl a =>
        refine ⟨σ.symm ((X.Fu u).fvec a), ?_, by simp⟩
        induction a using Fin.lastCases with
        | last =>
          have e : σ.symm ((X.Fu u).fvec (Fin.last _)) =
              (X.Fu u).z + (σ.symm (X.Fu u).z - (X.Fu u).z) := by
            simp [FlagG.fvec, Fin.snoc_last]
          rw [e]
          exact Submodule.add_mem _ (z_mem_Asp _ _) (X_le_Asp _ _ (SRat_inv (lf D (X.Fu u)) hσ).2.2)
        | cast a =>
          simp only [FlagG.fvec, Fin.snoc_castSucc]
          refine X_le_Asp _ _ (X_pres (lf D (X.Fu u)) (SRat_inv (lf D (X.Fu u)) hσ).2.1 _ ?_)
          exact Submodule.subset_span ⟨a, rfl⟩
      | inr b =>
        refine ⟨t1.lin (s' ((X.Fu u').fvec b)), ?_, ?_⟩
        · induction b using Fin.lastCases with
          | last =>
            have e : t1.lin (s' ((X.Fu u').fvec (Fin.last _))) =
                t1.frame.fl.z + t1.lin (s' (X.Fu u').z - (X.Fu u').z) := by
              rw [frame_z_eq_lin_zu, map_sub]; simp [FlagG.fvec, Fin.snoc_last]
            rw [e]
            refine Submodule.add_mem _ hz1A (hX1A ((mem_frameX Y t1 _).2 ?_))
            rw [LinearEquiv.symm_apply_apply]
            exact hs'.2.2
          | cast b =>
            refine hX1A ((mem_frameX Y t1 _).2 ?_)
            rw [LinearEquiv.symm_apply_apply]
            simp only [FlagG.fvec, Fin.snoc_castSucc]
            exact X_pres (lf D (X.Fu u')) hs'.2.1 _ (Submodule.subset_span ⟨b, rfl⟩)
        · show σ (t1.lin (s' ((X.Fu u').fvec b))) = t2.frame.fl.fvec b
          rw [frame_fvec, he]
          rfl
    intro w hw
    have hσw : σ w ∈ Hp t0.lam (lf D (X.Fu u)) t2.frame := by
      rw [hH2]
      refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun y hy => ?_
      obtain ⟨a, ha, rfl⟩ := hAsp hy
      rw [LinearEquiv.coe_coe, hσi]
      exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).1 hw a ha
    rw [← hTh] at hσw
    obtain ⟨p, hp, hp1⟩ := Submodule.mem_map.1 hσw
    obtain ⟨-, hp2, hp12, hpβ⟩ := (CorankRelation.mem_ThPairs t0.lam _ t2.frame t1.frame _ p).1 hp
    simp only [LinearMap.fst_apply] at hp1
    refine ⟨p.2, by rw [← hH1]; exact hp2, ?_, ?_⟩
    · rw [← hp1]; exact hp12
    · have e : (t1.lin * t2.lin⁻¹) p.1 = (t1.lin * s'⁻¹ * t1.lin⁻¹) w := by
        rw [hp1]
        show t1.lin (t2.lin.symm (σ w)) = t1.lin (s'.symm (t1.lin.symm w))
        rw [hsymm]
      rw [← e]
      exact hpβ

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option maxHeartbeats 1600000

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem lemmaG3_of_coefficients (hT : 3 ≤ Tu D u) (hT' : 3 ≤ Tu D u') (t0 t1 t2 : TauC Y u u') (h0 : Gt t0 ≠ 0) (h1 : Gt t1 ≠ 0)
    (h2 : Gt t2 ≠ 0) (hR1 : RelC Y u u' t0 t1) (hR2 : RelC Y u u' t0 t2) (hG1 : t1.G = t0.G) (hG2 : t2.G = t0.G)
    (σ s' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ SRat (lf D (X.Fu u))) (hs' : s' ∈ SRat (lf D (X.Fu u')))
    (he : t2.lin = σ * t1.lin * s') (ha : coefA Y u u' t0 t1 = coefA Y u u' t0 t2)
    (ha' : coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2) :
    nmlOf Y u u' t1 = nmlOf Y u u' t2 := by
  obtain ⟨iω, iς, i3⟩ := lemmaG3_of_inputs Y hT hT' t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 σ s' hσ hs' he ha ha'
  have hγ1 : t1.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t1.rep.2.2.1
  have hGF1 : Gflag (X.Fu u) t1.frame.fl ≠ 0 := G_ne_of_Gt Y h1
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hTE' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hσ' := SRat_inv (lf D (X.Fu u)) hσ
  have hs'' := SRat_inv (lf D (X.Fu u')) hs'
  set ς := t1.lin * s'⁻¹ * t1.lin⁻¹ with hς
  have hςx : ∀ x, ς x = t1.lin (s'.symm (t1.lin.symm x)) := fun x => rfl
  have hςf : ∀ x ∈ t1.frame.fl.X, ς x - x ∈ t1.frame.fl.X := by
    intro x hx
    refine (mem_frameX Y t1 _).2 ?_
    have hx0 := (mem_frameX Y t1 x).1 hx
    rw [map_sub, hςx, LinearEquiv.symm_apply_apply]
    exact Submodule.sub_mem _ (X_pres (lf D (X.Fu u')) hs''.2.1 _ hx0) hx0
  have hςz : ς t1.frame.fl.z - t1.frame.fl.z ∈ t1.frame.fl.X := by
    refine (mem_frameX Y t1 _).2 ?_
    rw [map_sub, hςx, LinearEquiv.symm_apply_apply, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply]
    exact hs''.2.2
  obtain ⟨τ, hτi, hτA, P1, P2⟩ := tau_exists (X.Fu u) t1.frame.fl hGF1 hTE (star_natCast _) hTE' (star_natCast _)
    σ ς hσ.1 (fun x hx => Submodule.sub_mem _ (X_pres (lf D (X.Fu u)) hσ.2.1 x hx) hx)
    (fun x hx => X_pres (lf D (X.Fu u)) hσ'.2.1 x hx) hσ.2.2 hςf hςz iω iς i3
  have hτX : ∀ x ∈ (X.Fu u).X, τ x = x := fun x hx => hτA x (X_le_Asp _ _ hx)
  have hτX1 : ∀ x ∈ t1.frame.fl.X, τ x = x := fun x hx => hτA x (by rw [← Asp_symm]; exact X_le_Asp _ _ hx)
  have hτs : ∀ x ∈ (X.Fu u).X, τ.symm x = x := fun x hx => by
    conv_lhs => rw [← hτX x hx]
    simp
  set n := σ * τ⁻¹ with hn
  set n' := t1.lin⁻¹ * τ * t1.lin * s' with hn'
  have hnN : n ∈ NRat (lf D (X.Fu u)) := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem hσ.1 ((Formalism.HermitianLatticesTheory.isom _).inv_mem hτi), fun j x hx => ?_, fun y hy => ?_⟩
    · have hxX : x ∈ (X.Fu u).X := Xflag_le_X (lf D (X.Fu u)) (j + 1) hx
      show σ (τ.symm x) - x ∈ _
      rw [hτs x hxX]
      exact hσ.2.1 j x hx
    · have hτi' : τ.symm ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := (Formalism.HermitianLatticesTheory.isom _).inv_mem hτi
      have hz : τ.symm y ∈ orth (VS D) (Xsp (lf D (X.Fu u))) :=
        perp_pres (lf D (X.Fu u)) hτi' (fun x hx => by rw [LinearEquiv.symm_symm, hτX x hx]; exact hx) y hy
      have := P1 _ hz
      rw [LinearEquiv.apply_symm_apply] at this
      show σ (τ.symm y) - y ∈ _
      rw [← neg_sub]
      exact Submodule.neg_mem _ this
  have hn'N : n' ∈ NRat (lf D (X.Fu u')) := by
    refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem
      ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ1) hτi) hγ1) hs'.1, fun j x hx => ?_, fun y hy => ?_⟩
    · have hxX : x ∈ (X.Fu u').X := Xflag_le_X (lf D (X.Fu u')) (j + 1) hx
      have hsx : s' x ∈ (X.Fu u').X := X_pres (lf D (X.Fu u')) hs'.2.1 x hxX
      have h1x : t1.lin (s' x) ∈ t1.frame.fl.X := (mem_frameX Y t1 _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hsx)
      show t1.lin.symm (τ (t1.lin (s' x))) - x ∈ _
      rw [hτX1 _ h1x, LinearEquiv.symm_apply_apply]
      exact hs'.2.1 j x hx
    · have hsy : s' y ∈ orth (VS D) (Xsp (lf D (X.Fu u'))) :=
        perp_pres (lf D (X.Fu u')) hs'.1 (fun x hx => X_pres (lf D (X.Fu u')) hs''.2.1 x hx) y hy
      have hv : t1.lin (s' y) ∈ Lat.orth (VS D) t1.frame.fl.X := by
        refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_
        rw [show x = t1.lin (t1.lin.symm x) by simp, hγ1]
        exact (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).1 hsy _ ((mem_frameX Y t1 x).1 hx)
      have h := P2 _ hv
      rw [hςx, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h
      have h' := (mem_frameX Y t1 _).1 h
      rw [map_sub, LinearEquiv.symm_apply_apply] at h'
      exact h'
  have heq : t2.lin = n * t1.lin * n' := by
    rw [he, hn, hn']
    group
  ext δ
  constructor
  · rintro ⟨m, hm, m', hm', rfl⟩
    refine ⟨m * n⁻¹, NRat_mul _ hm (NRat_inv _ hnN), n'⁻¹ * m', NRat_mul _ (NRat_inv _ hn'N) hm', ?_⟩
    rw [heq]
    group
  · rintro ⟨m, hm, m', hm', rfl⟩
    refine ⟨m * n, NRat_mul _ hm hnN, n' * m', NRat_mul _ hn'N hm', ?_⟩
    rw [heq]
    group

theorem normalsLemmaG3_holds : UnitaryNormalVectorCount := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hc t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 hσs ha ha' => ?_⟩
  obtain ⟨σ, hσ, s', hs', he⟩ := hσs
  have hT : 3 ≤ Tu D u ∧ 3 ≤ Tu D u' := by
    clear * - hc
    unfold Ctx at hc
    obtain ⟨-, -, -, h3, h3', -⟩ := hc.2.1
    exact ⟨h3, h3'⟩
  exact lemmaG3_of_coefficients Y hT.1 hT.2 t0 t1 t2 h0 h1 h2 hR1 hR2 hG1 hG2 σ s' hσ hs' he ha ha'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

section Uni

variable {K : Type*} [Field K] {N : ℕ}

theorem upUni_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A) (hB : IsUpUni B) : IsUpUni (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hA i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji (not_lt.1 hk)), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hA i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · simp

theorem loUni_iff_ct {A : Matrix (Fin N) (Fin N) K} [StarRing K] : IsLoUni A ↔ IsUpUni Aᴴ := by
  constructor
  · intro h i j
    refine ⟨fun hji => ?_, fun hij => ?_⟩
    · rw [conjTranspose_apply, (h j i).1 hji, star_zero]
    · subst hij; rw [conjTranspose_apply, (h i i).2 rfl, star_one]
  · intro h i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · have := (h j i).1 hij
      rw [conjTranspose_apply] at this
      exact star_eq_zero.1 this
    · subst hij
      have := (h i i).2 rfl
      rw [conjTranspose_apply] at this
      rw [← star_star (A i i), this, star_one]

theorem upUni_det {A : Matrix (Fin N) (Fin N) K} (h : IsUpUni A) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  · intro i j hij
    exact (h i j).1 hij

theorem loUni_det {A : Matrix (Fin N) (Fin N) K} (h : IsLoUni A) : A.det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  · intro i j hij
    exact (h i j).1 hij

theorem upUni_inv {A : Matrix (Fin N) (Fin N) K} (h : IsUpUni A) : IsUpUni A⁻¹ := by
  have hdet : IsUnit A.det := by rw [upUni_det h]; exact isUnit_one
  have hbt : A.BlockTriangular id := fun i j hij => (h i j).1 hij
  haveI := A.invertibleOfIsUnitDet hdet
  have hbt' : A⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  intro i j
  refine ⟨fun hji => hbt' hji, fun hij => ?_⟩
  subst hij
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv A hdet) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul] at e
  · simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [(h i k).1 hlt, zero_mul]
    · rw [hbt' hgt, mul_zero]
  · simp

theorem loUni_mul {A B : Matrix (Fin N) (Fin N) K} [StarRing K] (hA : IsLoUni A) (hB : IsLoUni B) :
    IsLoUni (A * B) := by
  rw [loUni_iff_ct, conjTranspose_mul]
  exact upUni_mul (loUni_iff_ct.1 hB) (loUni_iff_ct.1 hA)

theorem loUni_inv {A : Matrix (Fin N) (Fin N) K} [StarRing K] (h : IsLoUni A) : IsLoUni A⁻¹ := by
  rw [loUni_iff_ct, conjTranspose_nonsing_inv]
  exact upUni_inv (loUni_iff_ct.1 h)

theorem upUni_last {r : ℕ} {A : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni A) (c : Fin (r + 1)) :
    A (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  by_cases hc : c = Fin.last r
  · subst hc; rw [if_pos rfl]; exact (h _ _).2 rfl
  · rw [if_neg hc]
    exact (h _ _).1 (lt_of_le_of_ne (Fin.le_last c) hc)

end Uni

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem flag_of_upUni (F : FlagG S r T) (g : S.V →ₗ[E] S.V) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hN : IsUpUni N) (hg : ∀ b, g (F.fvec b) = ∑ c, N c b • F.fvec c) :
    (∀ j, ∀ x ∈ F.Xa (j + 1), g x - x ∈ F.Xa j) ∧ g F.z - F.z ∈ F.X := by
  have hdiff : ∀ b, g (F.fvec b) - F.fvec b = ∑ c ∈ Finset.univ.filter (· < b), N c b • F.fvec c := by
    intro b
    rw [hg b, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· < b)]
    have h2 : ∑ c ∈ Finset.univ.filter (fun c => ¬ c < b), N c b • F.fvec c = F.fvec b := by
      rw [Finset.sum_eq_single b]
      · rw [(hN b b).2 rfl, one_smul]
      · intro c hc hcb
        have : b < c := lt_of_le_of_ne (not_lt.1 (Finset.mem_filter.1 hc).2) (Ne.symm hcb)
        rw [(hN c b).1 this, zero_smul]
      · intro hb; exfalso; apply hb; simp
    rw [h2]; abel
  have he : ∀ a : Fin r, g (F.e a) - F.e a ∈ F.Xa a := by
    intro a
    have := hdiff (Fin.castSucc a)
    simp only [FlagG.fvec, Fin.snoc_castSucc] at this
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc' : c < Fin.castSucc a := (Finset.mem_filter.1 hc).2
    have hcl : c ≠ Fin.last r := ne_of_lt (lt_trans hc' (Fin.castSucc_lt_last a))
    obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hcl
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.subset_span ⟨c', by simpa using hc', rfl⟩
  refine ⟨fun j x hx => ?_, ?_⟩
  · induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      have ha' : (a : ℕ) < j + 1 := ha
      refine Submodule.span_mono ?_ (he a)
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨i, by show (i : ℕ) < j; have : (i : ℕ) < a := hi; omega, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), add_sub_add_comm]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hx
  · have := hdiff (Fin.last r)
    simp only [FlagG.fvec, Fin.snoc_last] at this
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hcl : c ≠ Fin.last r := ne_of_lt (Finset.mem_filter.1 hc).2
    obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hcl
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.subset_span ⟨c', rfl⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
