module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSConst

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPRealInv
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

def JDRInvFn : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) (p : B.SS k r), D.inSS p →
    ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ((r + k : ℕ) : ℕ∞) (B.GV k r) F →
      ∀ g ∈ B.GPos D, rhatOp k r D.z D.z' Y (B.rho D p F) g = B.rho D p (rhatOp k r D.z D.z' Y F) g

section poly

open Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra

variable {k r : ℕ}

theorem ri_mul_left {a : ℕ} {P : Q.Mx k r → ℂ} (c : ℂ) (h : U.IsPolyDeg a P) :
    U.IsPolyDeg a (fun g => c * P g) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨MvPolynomial.C c * q, ?_, fun g => by simp [hP g]⟩
  calc (MvPolynomial.C c * q).totalDegree ≤ (MvPolynomial.C c).totalDegree + q.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ a := by simp [hq]

theorem ri_mul_right {a : ℕ} {P : Q.Mx k r → ℂ} (h : U.IsPolyDeg a P) (c : ℂ) :
    U.IsPolyDeg a (fun g => P g * c) := by
  obtain ⟨q, hq, hP⟩ := h
  refine ⟨q * MvPolynomial.C c, ?_, fun g => by simp [hP g]⟩
  calc (q * MvPolynomial.C c).totalDegree ≤ q.totalDegree + (MvPolynomial.C c).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ a := by simp [hq]

theorem ri_ginv (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => (ginvH k r g *ᵥ v) p) := by
  have hdeg : ∀ (a : ℂ) (i : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))),
      (MvPolynomial.C a * MvPolynomial.X i : MvPolynomial _ ℂ).totalDegree ≤ 1 := fun a i =>
    (MvPolynomial.totalDegree_mul _ _).trans (by simp)
  refine ⟨∑ c, ∑ b, ∑ a, MvPolynomial.C (Hpk k r p a * Hpk k r b c * v c) * MvPolynomial.X (Sum.inr (b, a)),
    ?_, fun g => ?_⟩
  · exact (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ =>
      (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun b _ =>
        (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun a _ => hdeg _ _)))
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [ginvH, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inr, Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring

theorem ri_colR (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (q p : Fin (2 * r + k + 1)) :
    U.IsPolyDeg 1 (fun g => colR k r z g J q p) := by
  by_cases h1 : (q : ℕ) < r
  · simp only [colR, dif_pos h1]
    exact ri_ginv _ p
  · by_cases h2 : (q : ℕ) = r
    · simp only [colR, dif_neg h1, dif_pos h2]
      exact ri_ginv z p
    · refine ⟨MvPolynomial.C (colR k r z 0 J q p), by simp, fun g => ?_⟩
      simp [colR, h1, h2]

theorem ri_beJ (z : Fin (2 * r + k + 1) → ℂ) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    U.IsPolyDeg (2 * r + k + 1) (fun g => beJ k r z g J) := by
  choose Pq hPdeg hPev using fun q p => ri_colR (k := k) (r := r) z J q p
  refine ⟨(Matrix.of fun p q => Pq q p).det, ?_, fun g => ?_⟩
  · rw [Matrix.det_apply']
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h0 : (((Equiv.Perm.sign σ : ℤ) : MvPolynomial
        ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ)).totalDegree = 0 := by
      have hc : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial
          ((Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1))) ℂ) =
          MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) := by simp
      rw [hc]
      exact MvPolynomial.totalDegree_C _
    rw [h0, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc ∑ i, (Matrix.of (fun p q => Pq q p) (σ i) i).totalDegree ≤ ∑ _i : Fin (2 * r + k + 1), 1 :=
          Finset.sum_le_sum fun i _ => hPdeg _ _
      _ = 2 * r + k + 1 := by simp
  · show (Matrix.of fun p q => colR k r z g J q p).det = _
    rw [RingHom.map_det]
    congr 1
    ext p q
    simp [RingHom.mapMatrix_apply, hPev]

end poly

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem ri_order_le {t κ : ℕ} : ∀ Θ : B.DiffOp k r Wp Wq, PolyOp t κ Θ → B.opOrder Θ ≤ t
  | [], _ => by simp [B.opOrder]
  | Tm :: Θ, h => by
    have h1 := (h Tm (List.mem_cons_self ..)).1
    have h2 := ri_order_le Θ fun T' hT' => h T' (List.mem_cons_of_mem _ hT')
    unfold B.opOrder at h2 ⊢
    simp only [List.map_cons, List.foldr_cons]
    exact max_le h1 h2

def riCat (Θs : Fin (k + 1) → B.DiffOp k r Wp Wq) : List (Fin (k + 1)) → B.DiffOp k r Wp Wq
  | [] => []
  | i :: l => Θs i ++ riCat Θs l

theorem riCat_poly {Θs : Fin (k + 1) → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i)) :
    ∀ l, PolyOp t κ (riCat Θs l)
  | [] => fun T hT => absurd hT List.not_mem_nil
  | i :: l => QMinOp.polyOp_append (h i) (riCat_poly h l)

theorem riCat_apply (Θs : Fin (k + 1) → B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    ∀ l, B.opApply (riCat Θs l) F g = (l.map fun i => B.opApply (Θs i) F g).sum
  | [] => by simp [riCat, B.opApply]
  | i :: l => by rw [riCat, QMinOp.opApply_append, riCat_apply Θs F g l, List.map_cons, List.sum_cons]

private theorem foldr_max_eq_max_foldr_max_zero : ∀ (L : List ℕ) (x : ℕ), L.foldr max x = max (L.foldr max 0) x := by
  intro L
  induction L with
  | nil => intro x; simp
  | cons y L ih => intro x; simp only [List.foldr_cons]; rw [ih x, max_assoc]

theorem riCat_order {Θs : Fin (k + 1) → B.DiffOp k r Wp Wq} {t κ : ℕ} (h : ∀ i, PolyOp t κ (Θs i))
    (ho : ∀ i, B.opOrder (Θs i) = t) (i : Fin (k + 1)) (l : List (Fin (k + 1))) :
    B.opOrder (riCat Θs (i :: l)) = t := by
  have hle : B.opOrder (riCat Θs l) ≤ t := ri_order_le _ (riCat_poly h l)
  have h1 := ho i
  simp only [B.opOrder] at h1 hle
  simp only [riCat, B.opOrder, List.map_append, List.foldr_append]
  rw [foldr_max_eq_max_foldr_max_zero, h1]
  exact max_eq_left hle

theorem ri_real (z z' : Fin (2 * r + k + 1) → ℂ) (Y ε : ℂ) :
    ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ε • rhatOp k r z z' Y F g := by
  have h : ∀ i : Fin (k + 1), ∃ Θ : B.DiffOp k r Wp Wq, PolyOp (r + k) (2 * r + k + 1) Θ ∧ B.opOrder Θ = r + k ∧
      ∀ (UU : Set (B.Mat k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ((r + k : ℕ) : ℕ∞) UU F →
        ∀ g ∈ UU, g ∈ B.GV k r → B.opApply Θ F g = ∑ J ∈ jSetR k r,
          (fun (J : Fin (r + k) → Fin (2 * r + k + 1)) (g : B.Mat k r) =>
            ε * (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' * beJ k r z g J)) J g •
            qminorOp (Q.EH k r) (rowsR k r i) J (Q.uC k r 0 Y) F g := fun i =>
    QMinOp.qminOpRep (jSetR k r) (rowsR k r i) (fun J => J) _
      (fun J _ => ri_mul_left _ (ri_mul_left _ (ri_beJ z J))) _
  choose Θs hP hO hR using h
  refine ⟨riCat Θs (List.finRange (k + 1)), riCat_poly hP _, ?_, ?_⟩
  · have e : List.finRange (k + 1) = (0 : Fin (k + 1)) :: (List.finRange k).map Fin.succ := List.finRange_succ
    rw [e]
    exact riCat_order hP hO _ _
  · intro UU F hF g hgU hg
    rw [riCat_apply, ← Fin.sum_univ_def]
    simp only [rhatOp, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hR i UU F hF g hgU hg]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [smul_smul]

end ops

theorem jDRRealInvP_of_inv (hI : JDRInvFn) : JDRRealInvP := by
  intro ε Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, hP, hO, hR⟩ := ri_real (Wp := Wp (S.pl v)) (Wq := Wq (S.pl v)) (T v).base.z (T v).base.z' (y : ℂ) ε
  have hn : 0 < 2 * S.G.r + S.G.k + 1 := by omega
  refine ⟨Θ, QMinOp.polyOp_mono hP (by omega) (Nat.le_mul_of_pos_left _ (by omega)), ?_, ?_⟩
  · intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV S.G.k S.G.r := hg.1
    have hsg : B.sgs p g ∈ B.GV S.G.k S.G.r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group (T v).base hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho (T v).base hp hF) g hgG hgG]
    have e2 : B.rho (T v).base p (B.opApply Θ F) g =
        B.rho (T v).base p (fun x => ε • rhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, hI S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base (y : ℂ) p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro U F hU hF g hg
    have hgG : g ∈ B.GV S.G.k S.G.r := by simpa [Q.Glev] using hg.1
    refine hR (Q.Glev S.G.k S.G.r 0 ∩ U) F ?_ g hg hgG
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hF g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun x hx hxG => he x hx ?_⟩
    simpa [Q.Glev] using hxG

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRConst
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

private theorem hsVec_finset_sum_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type} [Fintype ι]
    (c : ι → ℂ) (A : ι → Wq →L[ℂ] Wp) : B.hsVec (∑ i, c i • A i) = ∑ i, c i • B.hsVec (A i) := by
  ext j
  simp [B.hsVec]

private theorem hsVec_injective_apply {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A C : Wq →L[ℂ] Wp)
    (h : B.hsVec A = B.hsVec C) : A = C := by
  have h' : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = C (stdOrthonormalBasis ℂ Wq i) := fun i => by
    have := congrArg (fun v => v i) h
    simpa [B.hsVec] using this
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using h' i)

private theorem toSm_smul_hermitian_curvature (P : M.Par) (c : ℂ) (u : MA.Qp P.r P.TT → ℂ) :
    MA.toSm P (c • u) = c • MA.toSm P u := by
  unfold MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · rw [dite_eq_left hu, dite_eq_left (Subalgebra.smul_mem _ hu c)]
    rfl
  · rw [dite_eq_right hu]
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, smul_zero, dite_eq_left (Subalgebra.zero_mem _)]
      rfl
    · rw [smul_zero, dite_eq_right]
      intro hm
      apply hu
      have := Subalgebra.smul_mem _ hm c⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem radial_constant_of_point_and_line (hPt : GTKPt) (hLine : GTKLine) : GTRConst := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d h
  obtain ⟨Qr, hQ⟩ := hPt Wp Wq P Bs X d h
  obtain ⟨e1, he1F, -⟩ := gauge_kappa_of_point_line hPt hLine Wp Wq P Bs X d h
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [h.1.2.2.2.1, h.1.2.2.2.2.1]
    rfl
  set ζ0 : ℂ := ((|P.TT| + 1 : ℝ) : ℂ) with hζ0def
  have hζ0 : P.TT < Complex.normSq ζ0 := by
    rw [hζ0def, Complex.normSq_ofReal]
    nlinarith [le_abs_self P.TT, abs_nonneg P.TT]
  have hFib : ∀ ζ, P.TT < Complex.normSq ζ →
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro ζ hζ
    unfold NF.Fib
    rw [h.2.2.1.2 ζ ζ0 (hTT ▸ hζ) (hTT ▸ hζ0)]
  choose E hEmem hEQ hEnorm hEuniq using fun ρ => hLine Wp Wq P Bs X d h Qr hQ ζ0 hζ0 ρ
  have hEQ' : ∀ ρ σ, E ρ ∘SL Qr σ = if ρ = σ then E ρ else 0 := by
    intro ρ σ
    calc E ρ ∘SL Qr σ = (E ρ ∘SL Qr ρ) ∘SL Qr σ := by rw [hEQ ρ]
      _ = E ρ ∘SL (Qr ρ ∘SL Qr σ) := ContinuousLinearMap.comp_assoc _ _ _
      _ = _ := by
        rw [hQ.1 ρ σ]
        split_ifs <;> simp [hEQ ρ]
  have hinQ : ∀ ρ σ (C : Wq →L[ℂ] Wp), inner ℂ (B.hsVec (E ρ)) (B.hsVec (C ∘SL Qr σ)) =
      if ρ = σ then inner ℂ (B.hsVec (E ρ)) (B.hsVec C) else 0 := by
    intro ρ σ C
    rw [GTK.hs_comp_right _ _ _ (hQ.2.2.1 σ), hEQ' ρ σ]
    split_ifs
    · rfl
    · rw [GTK.hs_expand]
      simp
  have horth : ∀ ρ σ, inner ℂ (B.hsVec (E ρ)) (B.hsVec (E σ)) = if ρ = σ then 1 else 0 := by
    intro ρ σ
    have hh := hinQ ρ σ (E σ)
    rw [hEQ σ] at hh
    rw [hh]
    split_ifs with hρσ
    · subst hρσ
      exact hEnorm ρ
    · rfl
  have hv : Orthonormal ℂ (fun σ => B.hsVec (E σ)) := orthonormal_iff_ite.mpr horth
  have hw : Orthonormal ℂ (fun σ => B.hsVec (e1 σ ζ0)) := orthonormal_iff_ite.mpr (he1F.2 ζ0 hζ0).2.1
  have hspan1 : ∀ Y ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0,
      B.hsVec Y ∈ Submodule.span ℂ (Set.range (fun σ => B.hsVec (e1 σ ζ0))) := by
    intro Y hY
    rw [(he1F.2 ζ0 hζ0).2.2 Y hY, hsVec_finset_sum_smul]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hle : Submodule.span ℂ (Set.range (fun σ => B.hsVec (E σ))) ≤
      Submodule.span ℂ (Set.range (fun σ => B.hsVec (e1 σ ζ0))) := by
    rw [Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    exact hspan1 _ (hEmem σ)
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [finrank_span_eq_card hv.linearIndependent, finrank_span_eq_card hw.linearIndependent])
  have hexp : ∀ Y ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0,
      Y = ∑ σ, inner ℂ (B.hsVec (E σ)) (B.hsVec Y) • E σ := by
    intro Y hY
    have hm : B.hsVec Y ∈ Submodule.span ℂ (Set.range (fun σ => B.hsVec (E σ))) := heq ▸ hspan1 Y hY
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hm
    have hcoef : ∀ σ, inner ℂ (B.hsVec (E σ)) (B.hsVec Y) = c σ := by
      intro σ
      rw [← hc]
      exact hv.inner_right_fintype c σ
    apply hsVec_injective_apply
    rw [hsVec_finset_sum_smul]
    simp only [hcoef]
    exact hc.symm
  refine ⟨fun ρ _ => E ρ, ⟨fun ρ => contDiffOn_const, fun ζ hζ =>
    ⟨fun ρ => (hFib ζ hζ).symm ▸ hEmem ρ, horth, fun Y hY => hexp Y (hFib ζ hζ ▸ hY)⟩⟩, ?_, fun ρ ζ ζ' => rfl⟩
  intro f Φ
  funext ρ
  unfold trR MA.actA
  simp only [MA.kap, AlgHom.comp_apply, Matrix.diagonalAlgHom_apply, Matrix.diagonal_apply]
  have hR : rawR P Bs.μsec (fun ρ _ => E ρ) (↑((d.κ f).1 Φ)) ρ =
      f ρ • rawR P Bs.μsec (fun ρ _ => E ρ) (↑Φ) ρ := by
    funext q
    simp only [rawR, Pi.smul_apply, smul_eq_mul]
    rw [hQ.2.2.2 f Φ q, GTK.hs_comp_sum]
    simp only [hinQ, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  symm
  refine (Finset.sum_eq_single ρ ?_ ?_).trans ?_
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    rfl
  · intro hρ
    exact absurd (Finset.mem_univ ρ) hρ
  · rw [if_pos rfl, hR, toSm_smul_hermitian_curvature]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem radial_gauge_constant_holds : GTRConst := GTK.radial_constant_of_point_and_line gauge_kappa_pointwise_holds gauge_kappa_line_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTrans
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTRT

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

section vals

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_add (A C : Wq →L[ℂ] Wp) : B.hsVec (A + C) = B.hsVec A + B.hsVec C := by
  unfold B.hsVec
  ext i
  simp

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  ext i
  simp

theorem vl_add (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    SSC.vl P Bs e (Φ + Ψ) ρ q = SSC.vl P Bs e Φ ρ q + SSC.vl P Bs e Ψ ρ q := by
  unfold SSC.vl
  rw [SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]
  unfold rawR
  simp only [Submodule.coe_add, Pi.add_apply, hsVec_add, inner_add_right, mul_add]

theorem vl_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) [FiniteDimensional ℂ Wp]
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : IsFrameB P Bs e) (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    SSC.vl P Bs e (c • Φ) ρ q = c * SSC.vl P Bs e Φ ρ q := by
  unfold SSC.vl
  rw [SSTr.trR_apply P Bs hpl hk e he, SSTr.trR_apply P Bs hpl hk e he]
  unfold rawR
  simp only [Submodule.coe_smul, Pi.smul_apply, hsVec_smul, inner_smul_right]
  ring

end vals

theorem dzQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have h0 : MA.eulerQ (TT := P.TT) M.vz (1 : MA.SmQ P.r P.TT) = 0 := by
    have h := Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vz 1 1
    rw [mul_one, one_mul, mul_one] at h
    have h2 : MA.eulerQ (TT := P.TT) M.vz (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vz 1 =
        MA.eulerQ (TT := P.TT) M.vz 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  unfold dzQ MA.DAlg.dzP MA.DAlg.mkP
  have h0' : (MA.DQ P).ev M.vz 1 = 0 := h0
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0
  rw [h0', map_zero]

theorem dzbQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzbQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have h0 : MA.eulerQ (TT := P.TT) M.vzb (1 : MA.SmQ P.r P.TT) = 0 := by
    have h := Formalism.FourierDecayAlt.P.analytic_leibniz P.r P.TT M.vzb 1 1
    rw [mul_one, one_mul, mul_one] at h
    have h2 : MA.eulerQ (TT := P.TT) M.vzb (1 : MA.SmQ P.r P.TT) + MA.eulerQ (TT := P.TT) M.vzb 1 =
        MA.eulerQ (TT := P.TT) M.vzb 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h2
  unfold dzbQ MA.DAlg.dzbP MA.DAlg.mkP
  have h0' : (MA.DQ P).ev M.vzb 1 = 0 := h0
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0
  rw [h0', map_zero]

theorem theta_fst {V : Type} [AddCommGroup V] [Module ℂ V] (P : M.Par) (d : Q.NFData P (Q.Pr V)) (Φ : V) :
    (ThetaNF P d).1 Φ = d.L.ζ.1 (d.L.nab.1 Φ) + d.L.ζb.1 (d.L.nabs.1 Φ) +
      (d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Φ +
      d.L.TT • d.L.GGi.1 ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Φ) := by
  unfold ThetaNF
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTRT

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

theorem radial_gauge_transition_holds : GTRTrans := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hC ρ m hm ζ hζ
  classical
  have hpl := hyp.1
  have hk2 := hyp.2.1
  have hTT : 0 ≤ P.TT := (mul_pos hpl.1.T_pos hpl.1.T'_pos).le
  have hLTT : d.L.TT = ((P.TT : ℝ) : ℂ) := by
    rw [hyp.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2, hpl.2.2.2.1, hpl.2.2.2.2.1]
    rfl
  obtain ⟨Φ0, hΦ0, -⟩ := SSTr.exists_tr P Bs hpl hk2 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  set Ψ0 := (d.κ (dTy P ρ)).1 Φ0 with hΨ0
  have t0 : trR P Bs e Ψ0 ρ = 1 := by
    rw [hΨ0, hk (dTy P ρ) Φ0, hΦ0, actA_kap]
    simp [dTy]
  let q0 : MA.Qp P.r P.TT := ⟨((fun _ => (1 : ℂ)), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have v0 : SSC.vl P Bs e Ψ0 ρ q0 = 1 := by
    unfold SSC.vl
    rw [t0]
    rfl
  have t1 : trR P Bs e (d.L.nab.1 Ψ0) ρ = fnZ P (A ρ) := by
    rw [(hC Ψ0 ρ).1, t0, GTRT.dzQ_one P hTT, mul_one, zero_add]
  have t2 : trR P Bs e (d.L.nabs.1 Ψ0) ρ = fnZ P (B ρ) := by
    rw [(hC Ψ0 ρ).2, t0, GTRT.dzbQ_one P hTT, mul_one, neg_zero, zero_add]
  have v1 : SSC.vl P Bs e (d.L.nab.1 Ψ0) ρ q0 = A ρ ζ := by
    unfold SSC.vl
    rw [t1, fnZ_val P (hAB ρ).1]
  have v2 : SSC.vl P Bs e (d.L.nabs.1 Ψ0) ρ q0 = B ρ ζ := by
    unfold SSC.vl
    rw [t2, fnZ_val P (hAB ρ).2]

  have vm : SSC.vl P Bs e ((ThetaNF P d).1 Ψ0) ρ q0 = m := by
    unfold SSC.vl
    rw [hm Ψ0, t0, GTRT.dzQ_one P hTT, GTRT.dzbQ_one P hTT, mul_zero, mul_zero, sub_zero, zero_add]
    show m * 1 = m
    ring
  have v3 : SSC.vl P Bs e ((d.κ (fun ρ => ((rhoSum P ρ : ℝ) : ℂ))).1 Ψ0) ρ q0 = ((rhoSum P ρ : ℝ) : ℂ) := by
    rw [SSC.vl_kap P Bs d e hk, v0, mul_one]
  have v4 : SSC.vl P Bs e ((d.κ (fun ρ => ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ))).1 Ψ0) ρ q0 =
      ((2 * rhoSum P ρ - uSum P : ℝ) : ℂ) := by
    rw [SSC.vl_kap P Bs d e hk, v0, mul_one]
  clear_value Ψ0

  have hfn := fun Ψ => SSC.vl_fn P Bs X d hyp e Ψ ρ q0
  rw [GTRT.theta_fst, GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_add P Bs hpl hk2 e he,
    GTRT.vl_add P Bs hpl hk2 e he, GTRT.vl_smul P Bs hpl hk2 e he, (hfn _).1, (hfn _).2.1, (hfn _).2.2,
    v3, v4, v1, v2, hLTT] at vm
  have hq : q0.1.2 = ζ := rfl
  rw [hq] at vm
  have hG : (Complex.normSq ζ : ℂ) - (P.TT : ℂ) ≠ 0 := by
    have : P.TT < Complex.normSq ζ := hζ
    intro h0
    have h1 : ((Complex.normSq ζ - P.TT : ℝ) : ℂ) = 0 := by push_cast; exact h0
    have : Complex.normSq ζ - P.TT = 0 := by exact_mod_cast h1
    linarith
  rw [← vm]
  push_cast
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOrbitalBlock
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory

open Formalism.FourierDecayAlt.P.PBJ

section core

variable {k ρ ph m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem coreQ (σh : Equiv.Perm (Fin ph)) (dh : Fin ph → ℂ) (σb : Equiv.Perm (Fin m)) (db : Fin m → ℂ)
    (z z' : Fin (2 * (ph + m + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + m + ρ) → E) (γ : B.Mat k ρ)
    (hint : Integrable (fun ξ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) =>
        U.psiStar (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) z z' ξ •
          F (U.gaXi (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) ξ (fun a => a.elim0) γ))
      (U.muXi k (ph + m) 0 ρ (Fub.sigQ σh σb))) :
    U.PhiFun (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) z z' F (fun a => a.elim0) γ =
      U.PhiTop (p := m) (s := 0) U.betaU σb db
        (fun Z => U.PhiFun (p := ph) (s := m) k ρ σh dh z z' F Z γ) (fun x => x.elim0) := by
  set RR := U.RC k (ph + m) ρ × U.RC k (ph + m) ρ
  have sR := Dx2.SL.sigma_RC k (ph + m) ρ
  set μR : Measure RR := (U.muRC k (ph + m) ρ).prod (U.muRC k (ph + m) ρ)
  have s1 := Fub.sfXiH ph m σh
  have s2 := Fub.sfXiH m 0 σb
  have s3 : SFinite (U.muXiH (ph + m) 0 (Fub.sigQ σh σb)) := Fub.sfXiH (ph + m) 0 (Fub.sigQ σh σb)
  let g : RR × (U.XiH ph m σh × U.XiH m 0 σb) → E := fun y =>
    U.psiH U.betaU σb y.2.2 •
      (U.psiStar (p := ph) (s := m) k ρ σh z z' (y.1, y.2.1) • F (U.gaXi (p := ph) (s := m) k ρ σh dh (y.1, y.2.1)
        (Matrix.of.symm (U.ZjH (p := m) (s := 0) σb db y.2.2 (fun x => x.elim0))) γ))
  let Φ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) ≃ᵐ RR × (U.XiH ph m σh × U.XiH m 0 σb) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl RR) (Fub.xiE σh σb)
  have hΦ : MeasurePreserving Φ (U.muXi k (ph + m) 0 ρ (Fub.sigQ σh σb)) (μR.prod (volume.prod volume)) :=
    (MeasurePreserving.id μR).prod (Fub.xiE_mp σh σb)
  have hfg : (fun ξ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) =>
      U.psiStar (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) z z' ξ •
        F (U.gaXi (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) ξ (fun a => a.elim0) γ)) = g ∘ Φ := by
    funext ξ
    obtain ⟨x, ⟨a0, b0⟩, v, u⟩ := ξ
    rw [Function.comp_apply]
    rw [show Φ (x, ((a0, b0), v, u)) = (x, Fub.xiE σh σb ((a0, b0), v, u)) from rfl, Fub.xiE_apply]
    simp only [g, U.psiStar, U.gaXi, U.ZjH, Dx2.SL.zj_zero, Fub.zj_split, Equiv.apply_symm_apply]
    rw [Fub.psiH_split σh σb U.betaU a0 b0 (Dx2.SL.uniqueT m).toInhabited.default v u, smul_smul]
    congr 1
    have e1 : Formalism.QuantumDeterminants.psi k (ph + m + 0 + ρ) z cStd (U.Rn k (ph + m + 0) ρ x.1) =
        Formalism.QuantumDeterminants.psi k (ph + m + ρ) z cStd (U.Rn k (ph + m) ρ x.1) := rfl
    have e2 : Formalism.QuantumDeterminants.psi k (ph + m + 0 + ρ) z' cStd (U.Rn k (ph + m + 0) ρ x.2) =
        Formalism.QuantumDeterminants.psi k (ph + m + ρ) z' cStd (U.Rn k (ph + m) ρ x.2) := rfl
    rw [e1, e2]
    ring
  have hg : Integrable g (μR.prod (volume.prod volume)) := by
    have := hint; rw [hfg] at this
    exact (hΦ.integrable_comp_emb Φ.measurableEmbedding).mp this
  have hL : U.PhiFun (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) z z' F (fun a => a.elim0) γ =
      ∫ y, g y ∂(μR.prod (volume.prod volume)) := by
    unfold U.PhiFun
    rw [hfg]
    exact hΦ.integral_comp' g
  have hA : MeasurePreserving (MeasurableEquiv.prodAssoc : (RR × U.XiH ph m σh) × U.XiH m 0 σb ≃ᵐ _)
      ((μR.prod volume).prod volume) (μR.prod (volume.prod volume)) := Dx2.SL.assoc_mp μR volume volume
  let g' : (RR × U.XiH ph m σh) × U.XiH m 0 σb → E := fun w => g (w.1.1, (w.1.2, w.2))
  have eg : g ∘ (MeasurableEquiv.prodAssoc : (RR × U.XiH ph m σh) × U.XiH m 0 σb ≃ᵐ _) = g' := rfl
  have hg' : Integrable g' ((μR.prod volume).prod volume) := by
    rw [← eg]; exact (hA.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mpr hg
  have hA' : ∫ y, g y ∂(μR.prod (volume.prod volume)) = ∫ w, g' w ∂((μR.prod volume).prod volume) :=
    (hA.integral_comp' g).symm
  rw [hL, hA', MeasureTheory.integral_prod_symm g' hg']
  unfold U.PhiTop
  rw [show U.muXiH m 0 σb = volume from rfl]
  congr 1
  funext η
  change (∫ x, U.psiH U.betaU σb η • _ ∂(μR.prod volume)) = _
  rw [integral_smul]
  rfl

end core

section wrap

theorem partner_two (h : C.LPt) (n : ℕ) (t c : ℂ) (a : ℕ) (ha : a < D.ptSize h + (n + 1 + 1)) :
    D.ptPartner (h ++ [(n + 1, t), (1, c)]) a =
      if a < D.ptSize h then D.ptPartner h a else if a < D.ptSize h + (n + 1) then D.ptSize h + (n - (a - D.ptSize h))
        else a := by
  rw [show h ++ [(n + 1, t), (1, c)] = (h ++ [(n + 1, t)]) ++ [(1, c)] by simp]
  rw [Dx2.SL.partner_append 1 c (h ++ [(n + 1, t)]) a (by rw [Dx2.SL.ptSize_append]; omega), Dx2.SL.ptSize_append]
  by_cases h1 : a < D.ptSize h + (n + 1)
  · rw [if_pos h1, Dx2.SL.partner_append (n + 1) t h a h1]
    by_cases h2 : a < D.ptSize h
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_pos h1]; omega
  · rw [if_neg h1, if_neg (by omega), if_neg h1]; omega

theorem scal_two (h : C.LPt) (n : ℕ) (t c : ℂ) (a : ℕ) (ha : a < D.ptSize h + (n + 1 + 1)) :
    D.ptScal (h ++ [(n + 1, t), (1, c)]) a =
      if a < D.ptSize h then D.ptScal h a else if a < D.ptSize h + (n + 1) then t else c := by
  rw [show h ++ [(n + 1, t), (1, c)] = (h ++ [(n + 1, t)]) ++ [(1, c)] by simp]
  rw [Dx2.SL.scal_append 1 c (h ++ [(n + 1, t)]) a (by rw [Dx2.SL.ptSize_append]; omega), Dx2.SL.ptSize_append]
  by_cases h1 : a < D.ptSize h + (n + 1)
  · rw [if_pos h1, Dx2.SL.scal_append (n + 1) t h a h1]
    by_cases h2 : a < D.ptSize h
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_pos h1]
  · rw [if_neg h1, if_neg (by omega), if_neg h1]

theorem kapB_mul (n : ℕ) :
    kapB n * ((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) ^ (Fintype.card (Fin (n + 1)) +
        (Fintype.card (G.UT (n + 1)) + Fintype.card (Fin (n + 1)))) : NNReal) : ℝ) = 1 := by
  rw [Dx2.SL.norm_betaU, show (2 : ℝ) / (2 * Real.pi) = 1 / Real.pi by field_simp, Dx2.SL.card_UT' n,
    Fintype.card_fin]
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN : (n + 1) * (n + 4) / 2 = n + 1 + ((n + 1) * n / 2 + (n + 1)) := by
    have h2 : 2 ∣ (n + 1) * n := (Nat.even_mul_pred_self (n + 1)).two_dvd
    obtain ⟨q, hq⟩ := h2
    have e : (n + 1) * (n + 4) = 2 * (q + 2 * (n + 1)) := by nlinarith
    rw [e, hq]; omega
  unfold kapB
  rw [NNReal.coe_pow, Real.coe_toNNReal _ (by positivity), hN, ← mul_pow, mul_one_div_cancel hp.ne', one_pow]

end wrap

section final

theorem sliceOmBlock : SliceOmBlock := by
  intro k r E _ _ _ z z' F h p n t c hp hle γ hloc hint
  subst hp
  have hP : D.ptSize (h ++ [(n + 1, t), (1, c)]) = D.ptSize h + (n + 1 + 1) := ptSize_two h n t c
  have hlocH : D.IsLocPt h (D.ptSize h) := ⟨fun b hb => hloc.1 b (List.mem_append_left _ hb), rfl⟩
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  set ph := D.ptSize h with hph
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t), (1, c)])),
      ((Fub.sigQ (D.ptPerm h) (Om.σB (n + 1))) (Fin.cast hP a)).val =
        (D.ptPerm (h ++ [(n + 1, t), (1, c)]) a).val := by
    intro a
    have ha : a.val < ph + (n + 1 + 1) := by have := a.isLt; omega
    rw [hspec a, partner_two h n t c a.val ha]
    by_cases h1 : a.val < ph
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (n + 1 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Fub.sigQ_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd ph ⟨a.val - ph, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, Fub.sigQ_natAdd, Fin.val_natAdd]
      by_cases h2 : a.val < ph + (n + 1)
      · rw [if_pos h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.castAdd 1 ⟨a.val - ph, by omega⟩ := Fin.ext rfl
        rw [e2, Om.σB, Fub.sigQ_castAdd, Fin.val_castAdd]
        simp only [Fin.revPerm_apply, Fin.val_rev]
        omega
      · rw [if_neg h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.natAdd (n + 1) (0 : Fin 1) :=
          Fin.ext (by simp; omega)
        rw [e2, Om.σB, Fub.sigQ_natAdd, Fin.val_natAdd]
        simp
        omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t), (1, c)])),
      Fub.dQ (D.ptDiag h) (Fub.dQ (fun _ : Fin (n + 1) => t) (fun _ : Fin 1 => c)) (Fin.cast hP a) =
        D.ptDiag (h ++ [(n + 1, t), (1, c)]) a := by
    intro a
    have ha : a.val < ph + (n + 1 + 1) := by have := a.isLt; omega
    simp only [D.ptDiag]
    rw [scal_two h n t c a.val ha]
    by_cases h1 : a.val < ph
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (n + 1 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Fub.dQ, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd ph ⟨a.val - ph, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, Fub.dQ, Fin.addCases_right]
      by_cases h2 : a.val < ph + (n + 1)
      · rw [if_pos h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.castAdd 1 ⟨a.val - ph, by omega⟩ := Fin.ext rfl
        rw [e2, Fub.dQ, Fin.addCases_left]
      · rw [if_neg h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.natAdd (n + 1) (0 : Fin 1) :=
          Fin.ext (by simp; omega)
        rw [e2, Fub.dQ, Fin.addCases_right]
  obtain ⟨hT1, hT2⟩ := Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t), (1, c)])) hP _ _ hσ _ _ hd
    (D.castV (by omega) z) (D.castV (by omega) z') (D.castF (by omega) F) γ
  have hc := coreQ (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t), (1, c)])) (D.ptPerm h) (D.ptDiag h) (Om.σB (n + 1))
    (Fub.dQ (fun _ : Fin (n + 1) => t) (fun _ : Fin 1 => c)) _ _ _ γ (hT1 hint)
  unfold D.sliceAt
  rw [dite_eq_left hle, hT2, hc, Om.omBlock_eq, smul_smul, ← Complex.ofReal_mul]
  rw [kapB_mul n, Complex.ofReal_one, one_smul]
  simp only [Dx2.SL.castV_castV, Dx2.SL.castF_castF]

end final

end Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory

theorem Formalism.FourierDecayAlt.P.slice_orbital_block : Formalism.FourierDecayAlt.P.FormNormSumIdentities.SliceOmBlock := Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory.sliceOmBlock
end
end
