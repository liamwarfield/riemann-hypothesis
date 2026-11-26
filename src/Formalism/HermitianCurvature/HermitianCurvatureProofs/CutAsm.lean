module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableLoc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutAsm
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelSystemAdmissibleSize
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Finset

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem prod_lamCfg (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (Y : ℝ) : ∏ s, (Y + lamCfg S v s) = S.P v Y := by
  show ∏ s : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
      (Y + (S.G.place (S.pl v)).lam ((s : ℕ) + 1)) = (S.G.place (S.pl v)).P Y
  have hm : (S.G.place (S.pl v)).k + (S.G.place (S.pl v)).m - 1 =
      (D.parOf S v).k + 2 * (D.parOf S v).r + 1 := by
    show S.G.k + (2 * S.G.r + 2) - 1 = S.G.k + 2 * S.G.r + 1
    omega
  rw [Sz.Cfg.P, hm]
  have e1 : ∏ s : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
      (Y + (S.G.place (S.pl v)).lam ((s : ℕ) + 1)) =
      ∏ i ∈ Finset.range ((D.parOf S v).k + 2 * (D.parOf S v).r + 1),
        (Y + (S.G.place (S.pl v)).lam (i + 1)) :=
    Fin.prod_univ_eq_prod_range (fun i => Y + (S.G.place (S.pl v)).lam (i + 1)) _
  rw [e1, Finset.range_eq_Ico, Finset.prod_Ico_add' (fun i => Y + (S.G.place (S.pl v)).lam i), zero_add]
  rfl

theorem level_system_admissible_size (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (hA : D.AdmAt S v a)
    (hI : ∀ x ∈ a, x.2 ∈ Set.Icc (S.cutLo v) (S.cutHi v)) (l : ℕ)
    (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
    (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT) (c : LE.Cut) (Lb : ℝ) :
    (MA.sysQ (D.parOf S v) l L j (lamCfg S v) (S.cutLo v) (S.cutHi v) Lb c S.Ntop).admitted a ∧
      (MA.sysQ (D.parOf S v) l L j (lamCfg S v) (S.cutLo v) (S.cutHi v) Lb c S.Ntop).size a = S.sizeAt v a := by
  obtain ⟨w, rfl⟩ := hA
  refine ⟨⟨fun x hx => hI x hx, ?_⟩, ?_⟩
  · rw [List.pairwise_iff_getElem]
    intro i i' hi hi' hii
    have := w.2.1.2 v i i' hi hi' (Nat.ne_of_lt hii) 0 (by norm_num) (by norm_num)
    simpa using this
  · show ((w.1 v).map fun x => |∏ s, (x.2 + lamCfg S v s)|).prod = _
    rw [C.HidaSetting.sizeAt]
    simp only [prod_lamCfg]

end defs

end

end Formalism.FourierDecayAlt.P.CutMP
end

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem isBuiltPlace_mono {Cc₁ Cc₂ : ℝ} (h : Cc₁ ≤ Cc₂) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {A₀ : ℝ} (hB : JCT.IsBuiltPlace Cc₂ S T f χ ν' m₀ top A₀) : JCT.IsBuiltPlace Cc₁ S T f χ ν' m₀ top A₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hB
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun v => le_trans ?_ (h8 v), le_trans h h9, h10, h11, le_trans ?_ h12, h13⟩
  · exact mul_le_mul_of_nonneg_right h (by positivity)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity)

theorem toSm_smul (P : M.Par) (c : ℂ) (u : MA.Qp P.r P.TT → ℂ) : MA.toSm P (c • u) = c • MA.toSm P u := by
  unfold Formalism.FourierDecayAlt.MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · rw [dite_eq_left hu, dite_eq_left (Subalgebra.smul_mem _ hu c)]
    rfl
  · rw [dite_eq_right hu, smul_zero]
    by_cases hc : c = 0
    · subst hc
      rw [dite_eq_left (by rw [zero_smul]; exact Subalgebra.zero_mem _)]
      exact Subtype.ext (by simp)
    · rw [dite_eq_right]
      intro h
      apply hu
      have h2 := Subalgebra.smul_mem _ h c⁻¹
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

theorem hsVec_smul {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (c : ℂ) (A : W →L[ℂ] V) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rfl

theorem trJ_smul (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (c : ℂ) (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    trJ S T v e (c • J) = c • trJ S T v e J := by
  funext ρ
  simp only [trJ, Pi.smul_apply, hsVec_smul, inner_smul_right]
  rw [← toSm_smul]
  congr 1
  funext q
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem trJ_congr (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (J J' : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (h : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, J (B.gq (T v).base x) = J' (B.gq (T v).base x)) :
    trJ S T v e J = trJ S T v e J' := by
  funext ρ
  simp only [trJ]
  congr 1
  funext q
  rw [h q.1 q.2]

def prFst (P : M.Par) : (MA.DQ P).Pr →+ (MA.DQ P).Op where
  toFun p := p.1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem pr_fst_sum (P : M.Par) {ι : Type} (s : Finset ι) (g : ι → (MA.DQ P).Pr) :
    (∑ i ∈ s, g i).1 = ∑ i ∈ s, (g i).1 := by
  exact map_sum (prFst P) g s

theorem pr_fst_smul (P : M.Par) (c : ℂ) (a : (MA.DQ P).Pr) : (c • a).1 = c • a.1 := by
  rfl

theorem op_sum_apply (P : M.Par) {ι : Type} (s : Finset ι) (g : ι → (MA.DQ P).Op) (y : (MA.DQ P).R) :
    (∑ i ∈ s, g i) y = ∑ i ∈ s, g i y := by
  first
  | exact LinearMap.sum_apply s g y
  | exact ContinuousLinearMap.sum_apply s g y
  | simp

theorem actA_mul (P : M.Par) (a b : MA.A P (MA.DQ P)) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (a * b) x = MA.actA P a (MA.actA P b x) := by
  funext π
  show ∑ π', ((a * b) π π').1 (x π') = ∑ σ, (a π σ).1 (∑ π', (b σ π').1 (x π'))
  have e : ∀ π', ((a * b) π π').1 (x π') = ∑ i, (a π i).1 ((b i π').1 (x π')) := by
    intro π'
    rw [Matrix.mul_apply, pr_fst_sum]
    first
      | exact (LinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
      | exact (ContinuousLinearMap.sum_apply _ _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
      | exact (op_sum_apply P Finset.univ _ _).trans (Finset.sum_congr rfl fun i _ => rfl)
      | (simp; rfl)
  rw [Finset.sum_congr rfl fun π' _ => e π', Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]

theorem actA_smul (P : M.Par) (c : ℂ) (a : MA.A P (MA.DQ P)) (x : M.Ty P → MA.SmQ P.r P.TT) :
    MA.actA P (c • a) x = c • MA.actA P a x := by
  funext π
  simp only [Formalism.FourierDecayAlt.MA.actA, Matrix.smul_apply, pr_fst_smul, Pi.smul_apply]
  rw [eq_comm]
  erw [Finset.smul_sum]
  symm
  refine Finset.sum_congr rfl fun π' _ => ?_
  first
    | exact LinearMap.smul_apply _ _ _
    | exact ContinuousLinearMap.smul_apply _ _ _
    | rfl

theorem actA_one (P : M.Par) (x : M.Ty P → MA.SmQ P.r P.TT) : MA.actA P 1 x = x := by
  classical
  funext π
  simp only [Formalism.FourierDecayAlt.MA.actA, Matrix.one_apply]
  erw [Finset.sum_eq_single π (fun b _ hb => by simp only [if_neg (Ne.symm hb)]; rfl)
    (fun h => absurd (Finset.mem_univ π) h)]
  simp only [if_pos rfl]
  rfl

theorem initial_coefficient_of_start_matrix (P : M.Par) (l : ℕ) (Y : ℂ) :
    Wd.C0 (MA.startM P (MA.DQ P) l).QQ (MA.sites P (MA.DQ P)) Y =
      M.sgn P l • Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) Y := by
  simp only [Formalism.FourierDecayAlt.Wd.C0, Formalism.FourierDecayAlt.MA.startM, Matrix.smul_apply, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum]

end asm

section main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem trJ_foldr (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hG : IsGauge S T v e)
    (hP : ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v), ∀ (Y : ℝ) (s : ℂ), s • Q.CV S.G.k S.G.r (Y : ℂ) J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) :
    ∀ (L : List (Bool × ℝ)) (J₀ : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), J₀ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) →
      L.foldr (fun x J => M.sgn (D.parOf S v) (S.l + 1) • Q.CV S.G.k S.G.r (x.2 : ℂ) J) J₀ ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧
      trJ S T v e (L.foldr (fun x J => M.sgn (D.parOf S v) (S.l + 1) • Q.CV S.G.k S.G.r (x.2 : ℂ) J) J₀) =
        MA.actA (D.parOf S v) ((L.map fun x => Wd.C0 (MA.startM (D.parOf S v) (MA.DQ (D.parOf S v)) (S.l + 1)).QQ
          (MA.sites (D.parOf S v) (MA.DQ (D.parOf S v))) (x.2 : ℂ)).prod) (trJ S T v e J₀) := by
  intro L J₀ hJ₀
  induction L with
  | nil =>
    refine ⟨hJ₀, ?_⟩
    simp only [List.foldr_nil, List.map_nil, List.prod_nil]
    rw [actA_one]
  | cons x L ih =>
    obtain ⟨hmem, htr⟩ := ih
    refine ⟨hP _ hmem x.2 _, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [trJ_smul, hG _ hmem x.2, ← actA_smul, ← initial_coefficient_of_start_matrix, htr, ← actA_mul]

end main

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPPCommPf
open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PCommPf

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq]

theorem isOpen_slice {Dc : (Fin r → ℂ) → Set (Q.Mx k r)}
    (ho : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1}) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    IsOpen (Dc c) := by
  have h := ho.preimage (continuous_const.prodMk continuous_id : Continuous (fun g : Q.Mx k r => (c, g)))
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨hc, hg⟩, fun hg => hg.2⟩

theorem tL_crd_comm (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Q.Mx k r))
    (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) (ho : IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1})
    (hΨ : Q.SmoothFam k r i {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} Ψ) (l : Fin r) (Y : ℂ) (a b : Fin 2)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r i) (hgD : g ∈ Dc c) :
    Q.crd (pOp l) (Q.QL k r z z' i Y a b Ψ) c g = Q.QL k r z z' i Y a b (Q.crd (pOp l) Ψ) c g ∧
    Q.crd (pbOp l) (Q.QL k r z z' i Y a b Ψ) c g = Q.QL k r z z' i Y a b (Q.crd (pbOp l) Ψ) c g := by
  have hO : IsOpen (Dc c) := isOpen_slice ho hc
  have hgG : g ∈ Q.Glev k r i ∩ Dc c := ⟨hg, hgD⟩
  have hx : ((c, g) : Qx8.XX k r) ∈ Qx8.UU Dc := ⟨hc, hgD⟩
  have hcd := Qx8.cd_tL (E := Wq →L[ℂ] Wp) (i := i) (U₀ := Qx8.UU Dc) ho z z' Y a b
  have hder : ∀ s s₂ : ℂ,
      s • ((1 / 2 : ℂ) • (Qx8.dv (Pi.single l 1) (fun c' => Q.tL k r z z' i Y a b (Ψ c')) c g +
        s₂ • Qx8.dv (Pi.single l Complex.I) (fun c' => Q.tL k r z z' i Y a b (Ψ c')) c g)) =
      Q.tL k r z z' i Y a b (fun g' => s • ((1 / 2 : ℂ) • (Qx8.dv (Pi.single l 1) Ψ c g' +
        s₂ • Qx8.dv (Pi.single l Complex.I) Ψ c g'))) g := by
    intro s s₂
    rw [hcd.comm _ Ψ hΨ (c, g) hx hg, hcd.comm _ Ψ hΨ (c, g) hx hg, smul_smul]
    have := Qx8.tl_comb (z := z) (z' := z') (i := i) Formalism.FourierDecayAlt.P.transfer_linear_local hO Y a b (s * (1 / 2)) s₂
      (Qx8.sf_slice (Qx8.sf_dv (Pi.single l 1) hΨ) hc)
      (Qx8.sf_slice (Qx8.sf_dv (Pi.single l Complex.I) hΨ) hc) hgG
    rw [← this]
    simp only [smul_smul]
  refine ⟨?_, ?_⟩
  · show pOp l (fun c' => Q.tL k r z z' i Y a b (Ψ c') g) c =
      Q.tL k r z z' i Y a b (fun g' => pOp l (fun c' => Ψ c' g') c) g
    have h := hder (c l) (-Complex.I)
    simp only [pOp, if_pos hc, wirt]
    simp only [Qx8.dv, neg_smul, ← sub_eq_add_neg] at h
    exact h
  · show pbOp l (fun c' => Q.tL k r z z' i Y a b (Ψ c') g) c =
      Q.tL k r z z' i Y a b (fun g' => pbOp l (fun c' => Ψ c' g') c) g
    have h := hder (star (c l)) Complex.I
    simp only [pbOp, if_pos hc, wirtBar]
    simp only [Qx8.dv] at h
    exact h

end PCommPf

theorem residue_projection_commutation : JDRPComm := by
  intro Wp Wq _ _ _ _ k r z z' π π' Dc Ψ _ _ ho hΨ l Y a b c hc g hg hgD
  exact (PCommPf.tL_crd_comm z z' (Fin.last r) Dc Ψ ho hΨ.1 l Y a b hc hg hgD).1

theorem crd_pbOp_QL_last_comm :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (Dc : (Fin r → ℂ) → Set (Q.Mx k r)) (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)), inWb k r z → inWb k r z' →
    IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} →
    Q.FamFF k r z z' π π' (Fin.last r) Dc Ψ →
    ∀ (l : Fin r) (Y : ℂ) (a b : Fin 2), ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c →
      Q.crd (Formalism.QuantumDeterminants.pbOp l) (Q.QL k r z z' (Fin.last r) Y a b Ψ) c g =
        Q.QL k r z z' (Fin.last r) Y a b (Q.crd (Formalism.QuantumDeterminants.pbOp l) Ψ) c g := by
  intro Wp Wq _ _ _ _ k r z z' π π' Dc Ψ _ _ ho hΨ l Y a b c hc g hg hgD
  exact (PCommPf.tL_crd_comm z z' (Fin.last r) Dc Ψ ho hΨ.1 l Y a b hc hg hgD).2

end Formalism.FourierDecayAlt.P.CutMP

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPhi
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem smoothLog_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) : ContDiffOn ℝ ∞ φ (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ ∞ (fun x : ℝ => φ (Real.exp (Real.log x))) (Set.Ioi 0) :=
    (hφ : ContDiff ℝ ∞ (fun u : ℝ => φ (Real.exp u))).comp_contDiffOn
      (Real.contDiffOn_log.mono fun x hx => (ne_of_gt (Set.mem_Ioi.1 hx)))
  exact h1.congr fun x hx => by rw [Real.exp_log (Set.mem_Ioi.1 hx)]

section mem

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem phi_mem_FFl (Bs : B.RealPlaceData k r Wp Wq) {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ)
    {Dm : Set (Q.Mx k r)} (hD : ∀ g ∈ Dm, 0 < Gf k r Bs.z Bs.z' g) {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm) :
    (fun g => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • J g) ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm := by
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    have hGc : Continuous (fun g : Q.Mx k r => Gf k r Bs.z Bs.z' g) :=
      (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').continuous
    refine ⟨U ∩ {g | 0 < Gf k r Bs.z Bs.z' g}, fun g => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ) • F g,
      hU.inter (isOpen_lt continuous_const hGc), ⟨hgU, hD g₀ hg₀.2⟩, ?_, ?_⟩
    · have hc : ContDiffOn ℝ ∞ (fun g : Q.Mx k r => ((φ (Gf k r Bs.z Bs.z' g) : ℝ) : ℂ))
          (U ∩ {g | 0 < Gf k r Bs.z Bs.z' g}) :=
        Complex.ofRealCLM.contDiff.comp_contDiffOn ((smoothLog_contDiffOn hφ).comp
          (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').contDiffOn fun g hg => hg.2)
      exact hc.smul (hF.mono Set.inter_subset_left)
    · intro g hgU hgG
      simp only [hFJ g hgU.1 hgG]
  · intro g hg n hn
    have e : Gf k r Bs.z Bs.z' (n * g) = Gf k r Bs.z Bs.z' g := by
      have := gf_SgS Bs (n_mem_Sset Bs.z hn) (one_mem_Sset Bs.z') g
      simpa using this
    simp only [e, hL g hg n hn]
    rw [smul_comm]
  · intro g hg n hn
    have e : Gf k r Bs.z Bs.z' (g * n) = Gf k r Bs.z Bs.z' g := by
      have := gf_SgS Bs (one_mem_Sset Bs.z) (n_mem_Sset Bs.z' hn) g
      simpa using this
    simp only [e, hR g hg n hn]
    rw [smul_comm]
  · intro g hg h hh h' hh'
    have e : Gf k r Bs.z Bs.z' (h * g * h') = Gf k r Bs.z Bs.z' g :=
      gf_SgS Bs (h_mem_Sset Bs.z hh) (h_mem_Sset Bs.z' hh') g
    simp only [e, hU g hg h hh h' hh']
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end mem

theorem phi_operator_transfer_holds : JAPhiOp := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he φ hφ J hJ
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun x hx => ⟨hx.1, hTT ▸ hx.2⟩
  have hOm : ∀ q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z', B.gq (T v).base q ∈ OmP S T v := by
    intro q hq
    have h := (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq).2
    exact ⟨h.2, fun a => h.1 _ (by simp)⟩
  have hJ' : J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) := hJ
  refine ⟨phi_mem_FFl (T v).base hφ (fun g (hg : g ∈ OmP S T v) => hg.1) hJ', ?_⟩
  funext ρ
  set u : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q =>
    ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) with hu_def
  have hu : u ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := by
    show ContDiffOn ℝ MA.sm (MA.ext u) (MA.Qset _ _)
    have hg : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => J (B.gq (T v).base x))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (cutTr_jgq_smooth (T v).base _ _ hJ'.1 hOm).mono hQ
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => e ρ x.2) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    have hwc : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r => MA.wq S.G.k x (D.parOf S v).TT) := by
      have hn := cutTr_normSq_contDiff
      unfold MA.wq
      fun_prop
    have hwp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.wq S.G.k x (D.parOf S v).TT ≠ 0 := by
      intro x hx
      unfold MA.wq
      exact (mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hx.1 l)) _)
        (pow_pos (sub_pos.2 hx.2) _)).ne'
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hwc.contDiffOn.sqrt hwp)
    refine (hw.mul ((cutTr_hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (cutTr_hsVec_contDiff.comp_contDiffOn hg))).congr ?_
    intro x hx
    simp [MA.ext, hx, hu_def]
  set p : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q => ((φ (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) with hp_def
  have hp : p ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := by
    show ContDiffOn ℝ MA.sm (MA.ext p) (MA.Qset _ _)
    have hG : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r =>
        (∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT)) := by
      have hn := cutTr_normSq_contDiff
      fun_prop
    have hGp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
        (∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT) ∈ Set.Ioi (0 : ℝ) := by
      intro x hx
      exact mul_pos (Finset.prod_pos fun l _ => Complex.normSq_pos.2 (hx.1 l)) (sub_pos.2 hx.2)
    have hc : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r =>
        ((φ ((∏ l, Complex.normSq (x.1 l)) * (Complex.normSq x.2 - (D.parOf S v).TT)) : ℝ) : ℂ))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn ((smoothLog_contDiffOn hφ).comp hG.contDiffOn hGp)
    refine hc.congr ?_
    intro x hx
    simp [MA.ext, hx, hp_def, MA.Gq]
  have hL : trJ S T v e (mulG S T v φ J) ρ = MA.toSm (D.parOf S v) (fun q => p q * u q) := by
    unfold trJ
    congr 1
    funext q
    rw [mulG, Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right, GfP,
      cutTr_Gf_gq (T v).base q.2.1 (hTT ▸ q.2.2)]
    simp only [hu_def, hp_def, MA.Gq, hTT]
    ring
  have hR : (trJ S T v e J ρ) = ⟨u, hu⟩ := by
    unfold trJ MA.toSm
    rw [dite_eq_left hu]
  have hP : MA.toSm (D.parOf S v) p = ⟨p, hp⟩ := by
    unfold MA.toSm
    rw [dite_eq_left hp]
  rw [hL, hR, hP]
  have hm : (fun q => p q * u q) ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := Subalgebra.mul_mem _ hp hu
  unfold MA.toSm
  rw [dite_eq_left hm]
  rfl

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCongrRight
open Matrix MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section comp

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]

theorem op_comp (b : Bool) {X : Mat k r} (hX : inLie k r X) {G : Mat k r → (ι → E)}
    (hG : CkOn ((1 : ℕ) : ℕ∞) (GV k r) G) (i : ι) {g : Mat k r} (hg : g ∈ GV k r) :
    P.B4.op b X (fun h => G h i) g = P.B4.op b X G g i := by
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hG g hg
  have hc0 : ContDiffOn ℝ (((0 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) f' U := by simpa using hc
  have e1 := P.B4.op_eq_op' 0 b hU hc0 hff hX g hgU hg
  let pr : (ι → E) →L[ℝ] E := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).restrictScalars ℝ
  have hc' : ContDiffOn ℝ (((0 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) (fun h => f' h i) U :=
    pr.contDiff.comp_contDiffOn hc0
  have hff' : ∀ h ∈ U, h ∈ GV k r → (fun h => G h i) h = (fun h => f' h i) h := fun h hU' hG' => by
    simp only [hff h hU' hG']
  have e2 := P.B4.op_eq_op' 0 b hU hc' hff' hX g hgU hg
  rw [e2, e1]
  unfold P.B4.op'
  have hd : DifferentiableAt ℝ f' g :=
    (hc0.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hfd : HasFDerivAt (fun h => f' h i) (pr.comp (fderiv ℝ f' g)) g :=
    pr.hasFDerivAt.comp g hd.hasFDerivAt
  rw [hfd.fderiv]
  rfl

theorem W_comp (w : List (Bool × Mat k r)) (hw : P.B4.AllLie w) {G : Mat k r → (ι → E)}
    (hG : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G) (i : ι) :
    ∀ g ∈ GV k r, P.B4.W w (fun h => G h i) g = P.B4.W w G g i := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    intro g hg
    have hw' : P.B4.AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hl : w.length ≤ (x :: w).length := by simp
    have hl1 : 1 + w.length ≤ (x :: w).length := by simp; omega
    rw [P.B4.W_cons, P.B4.W_cons,
      P.B4.op_congr x.1 (hw x List.mem_cons_self) (ih hw' (P.B4.ckOn_mono hl hG)) g hg]
    exact op_comp x.1 (hw x List.mem_cons_self) (P.B4.smooth_on_of_word_derivatives w hw' 1 (P.B4.ckOn_mono hl1 hG)) i hg

theorem ckOn_comp {m : ℕ∞} {G : Mat k r → (ι → E)} (hG : CkOn m (GV k r) G) (i : ι) :
    CkOn m (GV k r) (fun h => G h i) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hG g₀ hg₀
  let pr : (ι → E) →L[ℝ] E := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).restrictScalars ℝ
  exact ⟨U, fun h => f' h i, hU, hgU, pr.contDiff.comp_contDiffOn hc, fun g hg hgG => by simp only [hff g hg hgG]⟩

theorem ccle_comp {A c : ℝ} {m : ℕ} {G : Mat k r → (ι → E)} (hG : CCle A m G c) (i : ι) :
    CCle A m (fun h => G h i) c := by
  refine ⟨ckOn_comp hG.1 i, fun u v hu hv hl g hg => ?_⟩
  have hw : P.B4.AllLie (P.B4.lr u v) := by
    intro x hx
    simp only [P.B4.lr, List.mem_append, List.mem_map] at hx
    rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu X hX).1
    · exact (hv X hX).1
  have hlen : (P.B4.lr u v).length ≤ m := by simp [P.B4.lr]; omega
  have e : dLR u v (fun h => G h i) g = dLR u v G g i := by
    rw [P.B4.dLR_eq, P.B4.dLR_eq]
    exact W_comp _ hw (P.B4.ckOn_mono hlen hG.1) i g hg
  rw [e]
  refine le_trans ?_ (hG.2 u v hu hv hl g hg)
  have hgN : 0 ≤ gN g ^ A := Real.rpow_nonneg (Real.sqrt_nonneg _) A
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (dLR u v G g) i) hgN

end comp

section beta

open Formalism.FourierDecayAlt.P.JCx2 Filter

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem beta_congr_right (D : RealPlaceData k r Wp Wq) {F G G₂ : Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ GV k r, G g = G₂ g) : beta D F G = beta D F G₂ := by
  unfold B.beta betaBig
  refine integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ B.Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ GV k r := (hq hQ).1
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2)))) =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * inner ℂ (hsVec (JF D G₂ (bigCell k r q.1 (D.μsec q.2))))
        (hsVec (JF D F (bigCell k r q.1 (D.μsec q.2))))
    rw [sq_jf_congr D h hg]
  · have hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (sq_bcWeight_nonneg _ _ q)
    show (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _ = (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) * _
    rw [hw]
    simp

end beta

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.JCx2

theorem form_model : Formalism.FourierDecayAlt.P.FormNormSumIdentities.FormModel := by
  intro Wp Wq _ _ _ _ _ _ P0 T sg j w a mm ε' Sg hε' ha hmm hmm5 hSg V _ _ Mo
  let comp : V → Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := fun u e γ => Mo.ev u γ e
  have hcc : ∀ u e, CCle a mm (comp u e) ‖u‖ := fun u e => FormNormSumIdentities.ccle_comp (Mo.mem u) e
  have hin : ∀ u e, InCC a mm (comp u e) := fun u e => ⟨_, hcc u e⟩
  have hadd : ∀ u u', comp (u + u') = comp u + comp u' := by
    intro u u'; funext e γ; simp [comp, map_add (f := _)]
  have hsmul : ∀ (c : ℂ) u, comp (c • u) = c • comp u := by
    intro c u; funext e γ; simp [comp, map_smul]
  have hzero : comp 0 = 0 := by funext e γ; simp [comp]
  have hS := fun x x' y c hx hx' hy => JCx4.formLev_sesq_core P0 T sg j w a mm ha hmm x x' y c hx hx' hy
  have h0l : ∀ u', D.formLev T sg j w 0 (comp u') = 0 := by
    intro u'
    have h := (hS (comp 0) (comp 0) (comp u') 1 (hin 0) (hin 0) (hin u')).1
    rw [hzero, one_smul, add_zero, one_mul] at h
    linear_combination -h
  have h0r : ∀ u, D.formLev T sg j w (comp u) 0 = 0 := by
    intro u
    have h := (hS (comp 0) (comp 0) (comp u) 1 (hin 0) (hin 0) (hin u)).2
    rw [hzero, one_smul, add_zero, map_one, one_mul] at h
    linear_combination -h
  let Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun u u' => D.formLev T sg j w (comp u) (comp u'))
    (fun u₁ u₂ u' => by
      rw [hadd]
      have h := (hS (comp u₁) (comp u₂) (comp u') 1 (hin u₁) (hin u₂) (hin u')).1
      rw [one_smul, one_mul] at h
      exact h)
    (fun c u u' => by
      simp only [RingHom.id_apply, smul_eq_mul]
      rw [hsmul]
      have h := (hS (comp 0) (comp u) (comp u') c (hin 0) (hin u) (hin u')).1
      rw [hzero, zero_add, h0l, zero_add] at h
      exact h)
    (fun u u₁ u₂ => by
      rw [hadd]
      have h := (hS (comp u₁) (comp u₂) (comp u) 1 (hin u₁) (hin u₂) (hin u)).2
      rw [one_smul, map_one, one_mul] at h
      exact h)
    (fun c u u' => by
      simp only [smul_eq_mul]
      rw [hsmul]
      have h := (hS (comp 0) (comp u') (comp u) c (hin 0) (hin u') (hin u)).2
      rw [hzero, zero_add, h0r, zero_add] at h
      exact h)
  obtain ⟨Cf, hCf0, hCf⟩ := JCx4.formLev_bound_mm P0 T sg j w a ha
  have hN0 : (0 : ℝ) ≤ (w.length : ℝ) := Nat.cast_nonneg _
  refine ⟨Bf, Real.sqrt Cf, Real.sqrt_nonneg _, fun u => ?_, ?_⟩
  · have hb := hCf (comp u) (comp u) ‖u‖ ‖u‖
      (fun b => pd_ccle_mono (by linarith) hmm5 (hcc u b))
      (fun b => pd_ccle_mono (by linarith) (by omega) (hcc u b))
    have e : Bf u u = D.formLev T sg j w (comp u) (comp u) := rfl
    rw [e]
    calc (D.formLev T sg j w (comp u) (comp u)).re ≤ ‖D.formLev T sg j w (comp u) (comp u)‖ := Complex.re_le_norm _
      _ ≤ Cf * ‖u‖ * ‖u‖ := hb
      _ = (Real.sqrt Cf * ‖u‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt hCf0]; ring
  · intro u u' x x' ε'' hε'' hx hx' hxu hxu'
    show D.formLev T sg j w (comp u) (comp u') = D.formLev T sg j w x x'
    unfold D.formLev
    refine Finset.sum_congr rfl fun e _ => ?_
    have hRR := JCx4.ma_hS P0 T sg j w
    have hmmU : 5 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length ≤ P5.mmUser P0 w.length :=
      pd_thr_mm P0 j w.length _ le_rfl
    have hinx : ∀ b, InCC (P5.Auser P0 w.length + 1) ((2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (x b) :=
      fun b => sq_inCC_mono le_rfl (by omega) (hx b).2.1
    have hinu : ∀ b, InCC (P5.Auser P0 w.length + 1) ((2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length) (comp u b) :=
      fun b => sq_inCC_mono ha (by omega) (hin u b)
    have hloc : ∀ g ∈ GV P0.k (P0.r - j), D.actOp (D.RRlev T sg j w) (comp u) e g =
        D.actOp (D.RRlev T sg j w) x e g := by
      intro g hg
      rw [JCx4.ma_actOp_eq, JCx4.ma_actOp_eq]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hA : P5.Auser P0 w.length + 1 - ((2 * w.length : ℕ) : ℝ) + ((2 * w.length : ℕ) : ℝ) =
          P5.Auser P0 w.length + 1 := by ring
      have hm : 0 + (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length =
          (2 * (P0.r - (j : ℕ)) + P0.k + 1) * w.length := by ring
      refine (hRR e b).2.2 (P5.Auser P0 w.length + 1 - ((2 * w.length : ℕ) : ℝ)) 0 (comp u b) (x b)
        (by rw [hA, hm]; exact hinu b) (by rw [hA, hm]; exact hinx b) (fun γ hγ => hxu b γ hγ) g hg
    rw [sq_beta_congr (T.bs j) hloc]
    exact FormNormSumIdentities.beta_congr_right (T.bs j) (fun γ hγ => hxu' e γ hγ)

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableBlockIntegrand
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory Filter

noncomputable section

section om

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem maxpow_le_onepow {x y a : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (ha : 0 ≤ a) :
    (1 + x) ^ (-a) ≤ (max 1 y) ^ (-a) := by
  refine Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le one_pos (le_max_left _ _)) ?_ (by linarith)
  exact max_le (by linarith) (by linarith)

theorem continuous_lowRow (n : ℕ) : Continuous (fun a : Fin n → ℂ => lowRow a) := by
  unfold lowRow
  exact P.G7.continuous_blk continuous_const continuous_const continuous_id continuous_const

theorem continuous_blkU (n : ℕ) :
    Continuous (fun p : (UT n → ℂ) × (Fin n → ℂ) => blk (upper p.1) p.2 0 1) :=
  P.G7.continuous_blk (P.Dx2.SL.cont_upper.comp continuous_fst) continuous_snd continuous_const continuous_const

theorem continuous_orbM (n : ℕ) (t c : ℂ) : Continuous (orbM n t c) := by
  unfold orbM
  refine Continuous.matrix_mul (Continuous.matrix_mul ((continuous_lowRow n).comp continuous_fst) continuous_const) ?_
  exact (continuous_blkU n).comp (continuous_snd)

theorem integrable_blockIntegrand (β : ℂ) (m : ℕ) (Φ : Mat (m + 2) → V) (t c : ℂ) (ht : t ≠ 0) (K a : ℝ)
    (ha : ((m : ℝ) + 1) * ((m : ℝ) + 4) < a) (hc : ∀ p, ContinuousAt Φ (orbM (m + 1) t c p))
    (hb : ∀ p, ‖Φ (orbM (m + 1) t c p)‖ ≤ K * (1 + ‖orbM (m + 1) t c p‖) ^ (-a)) :
    Integrable (blockIntegrand β (m + 1) Φ t c) (muBlock β (m + 1)) := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖orbM (m + 1) t c 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (orbM (m + 1) t c 0))]
  have hpt : ∀ p : BlockCoord (m + 1),
      ‖blockIntegrand β (m + 1) Φ t c p‖ ≤ K * (max 1 ‖coordMap (m + 1) t p‖) ^ (-a) := by
    intro p
    rw [P.OrbitTailEstimates.norm_blockIntegrand]
    refine (hb p).trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact maxpow_le_onepow (norm_nonneg _) (P.OrbitTailEstimates.norm_coordMap_le (m + 1) t c p) ha0
  obtain ⟨k, hk⟩ := P.G7.muBlock_eq β (m + 1)
  have i3 : BorelSpace (BlockCoord (m + 1)) := inferInstance
  have j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hfr : (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) < a := by
    rw [P.OrbitTailEstimates.finrank_block_cast]; exact ha
  have hI : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a)) (muBlock β (m + 1)) := by
    rw [hk]; exact (P.OrbitTailEstimates.integrable_maxpow volume a hfr).smul_measure_nnreal
  have hJ := P.G7.jacobian (m + 1) β t ht
  have hI' : Integrable (fun p : BlockCoord (m + 1) => (max 1 ‖coordMap (m + 1) t p‖) ^ (-a))
      (muBlock β (m + 1)) := by
    have h2 : Integrable (fun q : BlockCoord (m + 1) => (max 1 ‖q‖) ^ (-a))
        (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) := hJ ▸ hI.smul_measure_nnreal
    exact (P.G7.embedding_coordMap _ t ht).integrable_map_iff.1 h2
  have hcont : Continuous (blockIntegrand β (m + 1) Φ t c) := by
    unfold blockIntegrand
    refine Continuous.smul ?_ ?_
    · have h1 : Continuous fun p : BlockCoord (m + 1) => G.subSum (lowRow p.1) := by
        unfold G.subSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_lowRow (m + 1)).comp continuous_fst))
      have h2 : Continuous fun p : BlockCoord (m + 1) => G.superSum (blk (upper p.2.1) p.2.2 0 1) := by
        unfold G.superSum
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply _).comp ((continuous_apply _).comp ((continuous_blkU (m + 1)).comp continuous_snd))
      exact ((P.G7.continuous_psi β).comp h1).mul ((P.G7.continuous_psi β).comp h2)
    · exact continuous_iff_continuousAt.2 fun p => (hc p).comp (continuous_orbM (m + 1) t c).continuousAt
  exact (hI'.const_mul K).mono' hcont.aestronglyMeasurable (Eventually.of_forall hpt)

theorem integrable_longIntegrand (n : ℕ) (Φ : Mat (n + 1) → V) (z : ℂ) (hz : z ≠ 0) (K a : ℝ)
    (ha : (Module.finrank ℝ (UT (n + 1) → ℂ) : ℝ) < a)
    (hc : ∀ v, ContinuousAt Φ (P.JCTx6.Pos.Zv n z v))
    (hb : ∀ v, ‖Φ (P.JCTx6.Pos.Zv n z v)‖ ≤ K * (1 + ‖P.JCTx6.Pos.Zv n z v‖) ^ (-a)) :
    Integrable (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v))
      (muPi U.betaU (UT (n + 1))) := by
  have ha0 : 0 ≤ a := le_trans (Nat.cast_nonneg _) ha.le
  have hK : 0 ≤ K := by
    have h := hb 0
    by_contra hn
    have : K * (1 + ‖P.JCTx6.Pos.Zv n z 0‖) ^ (-a) < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hn) (Real.rpow_pos_of_pos (by positivity) _)
    linarith [norm_nonneg (Φ (P.JCTx6.Pos.Zv n z 0))]
  have hZc : Continuous (fun v : UT (n + 1) → ℂ => P.JCTx6.Pos.Zv n z v) := by
    show Continuous (fun v : UT (n + 1) → ℂ =>
      ((ptLong (n + 1) z * upper v : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Mat (n + 1)))
    exact continuous_const.matrix_mul P.Dx2.SL.cont_upper
  have hΦc : Continuous (fun v : UT (n + 1) → ℂ => Φ (P.JCTx6.Pos.Zv n z v)) :=
    continuous_iff_continuousAt.2 fun v => (hc v).comp hZc.continuousAt
  have hψc : Continuous (fun v : UT (n + 1) → ℂ => psi U.betaU (superSum (upper v))) := by
    have h1 : Continuous fun v : UT (n + 1) → ℂ => superSum (upper v) := by
      unfold superSum
      exact continuous_finsetSum _ fun i _ =>
        (continuous_apply _).comp ((continuous_apply _).comp P.Dx2.SL.cont_upper)
    exact (P.G7.continuous_psi _).comp h1
  have hbound : ∀ v : UT (n + 1) → ℂ, ‖psi U.betaU (superSum (upper v)) • Φ (P.JCTx6.Pos.Zv n z v)‖ ≤
      K * (min 1 ‖z‖) ^ (-a) * (1 + ‖v‖) ^ (-a) := by
    intro v
    rw [norm_smul, P.WirtingerIntegrationByParts.norm_psi, one_mul]
    refine (hb v).trans ?_
    have := mul_le_mul_of_nonneg_left (P.JCTx6.Pos.Zv_decay n hz v ha0) hK
    rw [← mul_assoc] at this
    exact this
  rw [P.Dx2.SL.muPi_betaU]
  apply Integrable.smul_measure_nnreal
  exact ((integrable_one_add_norm ha).const_mul (K * (min 1 ‖z‖) ^ (-a))).mono'
    (hψc.smul hΦc).aestronglyMeasurable (Eventually.of_forall hbound)

theorem clm_omBlock [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (t c : ℂ) (hI : Integrable (blockIntegrand β n Φ t c) (muBlock β n)) :
    L (OmBlock β n Φ t c) = OmBlock β n (fun Z => L (Φ Z)) t c := by
  unfold OmBlock
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [blockIntegrand, L.map_smul]

theorem clm_omLong [CompleteSpace V] [CompleteSpace W] (L : V →L[ℂ] W) (β : ℂ) (n : ℕ) (Φ : Mat (n + 1) → V)
    (z : ℂ) (hI : Integrable (fun v : UT (n + 1) → ℂ => psi β (superSum (upper v)) • Φ (ptLong (n + 1) z * upper v))
      (muPi β (UT (n + 1)))) :
    L (OmLong β n Φ z) = OmLong β n (fun Z => L (Φ Z)) z := by
  unfold OmLong
  rw [← L.integral_comp_comm hI]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [L.map_smul]

end om

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end
