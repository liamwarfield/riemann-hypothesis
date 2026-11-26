module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LimitOfModuleForms
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ResGContDiffAt

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelTransport
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SiteTransport
open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

section comp

variable {V V' V'' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V'']
  [Module ℂ V''] {T : V →ₗ[ℂ] V'} {T' : V' →ₗ[ℂ] V''}

theorem rel_comp {A : Pr V} {A' : Pr V'} {A'' : Pr V''} (h : Rel T A A') (h' : Rel T' A' A'') :
    Rel (T' ∘ₗ T) A A'' := by
  refine ⟨LinearMap.ext fun v => ?_, LinearMap.ext fun v => ?_⟩
  · have h1 := LinearMap.congr_fun h.1 v
    have h2 := LinearMap.congr_fun h'.1 (T v)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h2, h1]
  · have h1 := LinearMap.congr_fun h.2 v
    have h2 := LinearMap.congr_fun h'.2 (T v)
    simp only [LinearMap.comp_apply] at h1 h2 ⊢
    rw [h2, h1]

theorem mrel_comp {M : Matrix (Fin 2) (Fin 2) (Pr V)} {M' : Matrix (Fin 2) (Fin 2) (Pr V')}
    {M'' : Matrix (Fin 2) (Fin 2) (Pr V'')} (h : MRel T M M') (h' : MRel T' M' M'') : MRel (T' ∘ₗ T) M M'' :=
  fun a b => rel_comp (h a b) (h' a b)

variable {S : Type} [Fintype S] [DecidableEq S]

end comp

section bT

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem mrel_Ts {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) (Y : ℂ) : MRel T (Wd.Ts σ Y) (Wd.Ts σ' Y) := by
  unfold Wd.Ts; exact mrel_Tm Y hp hc hci

theorem arel_bT {σ : Wd.Site (Pr V)} {σ' : Wd.Site (Pr V')} (hp : Rel T σ.p σ'.p) (hc : Rel T σ.c σ'.c)
    (hci : Rel T σ.ci σ'.ci) : ∀ w : List (Wd.Letter ℂ S), ARel T (Wd.bT σ w) (Wd.bT σ' w)
  | [] => by unfold Wd.bT; exact arel_one
  | l :: w => by
    unfold Wd.bT Wd.vlet
    refine arel_mul (arel_ins _ (brel_lift0 ?_)) (arel_bT hp hc hci w)
    split_ifs
    · exact mrel_Ts hp hc hci _
    · intro a b
      rw [Matrix.map_apply, Matrix.map_apply]
      exact rel_star (mrel_Ts hp hc hci _ a b)

end bT

section one

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem site_ops {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (l : Fin ρ) :
    Rel (trL ht z z' π π') (L.p (shS l)) (Ls.p l) ∧ Rel (trL ht z z' π π') (L.c (shS l)) (Ls.c l) ∧
      Rel (trL ht z z' π π') (L.ci (shS l)) (Ls.ci l) := by
  have hop := fun (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  refine ⟨?_, ?_, ?_⟩
  · rw [hL.1, hLs.1]
    exact rel_mk (fun v => hop 0 v) (fun v => by simp only [LinearMap.neg_apply, hop 3, map_neg])
  · rw [hL.2.2.1, hLs.2.2.1]
    exact rel_mk (fun v => hop 1 v) (fun v => hop 4 v)
  · rw [hL.2.2.2.1, hLs.2.2.2.1]
    exact rel_mk (fun v => hop 2 v) (fun v => hop 5 v)

theorem qqi_rel_n {t : ℂ} (ht : t ≠ 0) (hz : inWb k ρ z) (hz' : inWb k ρ z')
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {st : Fr.Start (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'))}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    {sts : Fr.Start (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))))} {s : ℂ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y) (n : ℕ) (hn : n ≤ ρ) (Y : ℂ) :
    MRel (trL ht z z' π π') (P5.QQi L st ⟨n + 1, by omega⟩ Y) (P5.QQi Ls sts ⟨n, by omega⟩ Y) := by
  have hQ : MRel (trL ht z z' π π') (st.QQ Y) (sts.QQ Y) := by
    rw [hst, hsts]
    exact mrel_smul s fun a b => rel_mk (fun v => t_tr ht hz hz' X Xs Y a b v) (fun v => t_tr ht hz hz' X Xs _ b a v)
  unfold P5.QQi
  exact mrel_mul (mrel_mul (mrel_conjTranspose (tprod_rel ht hL hLs _ _ n rfl)) hQ) (tprod_rel ht hL hLs _ _ n rfl)

end one

end Formalism.FourierDecayAlt.P.PTieB

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB

end Formalism.FourierDecayAlt.P
end
end

open Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PTieL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH Formalism.FourierDecayAlt.P.PTieB

section id

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rel_id (A : Pr V) : Rel (LinearMap.id : V →ₗ[ℂ] V) A A :=
  ⟨by rw [LinearMap.comp_id, LinearMap.id_comp], by rw [LinearMap.comp_id, LinearMap.id_comp]⟩

theorem mrel_id (M : Matrix (Fin 2) (Fin 2) (Pr V)) : MRel (LinearMap.id : V →ₗ[ℂ] V) M M := fun _ _ => rel_id _

end id

theorem pairAt_smul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) (a : ℝ≥0)
    (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    P5.pairAt (a • μ) Φ Ψ c = ((a : ℝ) : ℂ) * P5.pairAt μ Φ Ψ c := by
  unfold P5.pairAt
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem glue_zero' {r : ℕ} (c : Fin r → ℂ) (c'' : Fin (r - 0) → ℂ) :
    P5.glue (⟨0, by omega⟩ : Fin (r + 1)) c (PTie.shiftCf ⟨0, by omega⟩ c'') = c'' := by
  funext l
  simp [P5.glue, PTie.shiftCf]

theorem glue_step {r : ℕ} (j : ℕ) (hj : j + 1 ≤ r) (c : Fin r → ℂ) (c'' : Fin (r - (j + 1)) → ℂ)
    (hn : r - j = 1 + (r - (j + 1))) :
    P5.glue (⟨j, by omega⟩ : Fin (r + 1)) c
        (PTie.shiftCf ⟨j, by omega⟩ (fun l => consC (c ⟨j, by omega⟩) c'' (Fin.cast hn l))) =
      P5.glue (⟨j + 1, by omega⟩ : Fin (r + 1)) c (PTie.shiftCf ⟨j + 1, by omega⟩ c'') := by
  funext l
  unfold P5.glue PTie.shiftCf consC
  by_cases h1 : j + 1 ≤ l.val
  · rw [dite_eq_left (show j ≤ l.val by omega), dite_eq_left h1]
    simp only [Fin.val_cast]
    rw [dite_eq_right (by omega)]
    congr 1
  · by_cases h2 : j ≤ l.val
    · rw [dite_eq_left h2, dite_eq_right h1]
      simp only [Fin.val_cast]
      rw [dite_eq_left (by omega)]
      congr 1
      ext
      simp only
      omega
    · rw [dite_eq_right h2, dite_eq_right h1]

theorem castM_iota0 {k r : ℕ} (h : 0 + (r - 0) = r) (g : B.Mat k (r - 0)) :
    D.castM h (ιLev k 0 (r - 0) g) = g := by
  ext p q
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, ιLev, finCongr_symm, finCongr_apply,
    Fin.val_cast]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem step_cast {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k n ρ : ℕ} (hn : n = 1 + ρ)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn.symm (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn.symm (liftVec k 1 ρ zs'))
    (hzs : inWb k ρ zs) (hzs' : inWb k ρ zs')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn.symm (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn.symm (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (st : Fr.Start (Pr (RadSp k n z z' π π')))
    (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ) (sts : Fr.Start (Pr (RadSp k ρ zs zs' πs πs')))
    (s : ℂ) (μ : Measure (Mt k n)) (μs : Measure (Mt k ρ))
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) (hst : ∀ Y, st.QQ Y = s • X.QQ Y)
    (hsts : ∀ Y, sts.QQ Y = s • Xs.QQ Y)
    (hμ : B.IsHaarOn (Glev k n (Fin.last n)) μ) (hμs : B.IsHaarOn (Glev k ρ (Fin.last ρ)) μs)
    (hlaw : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k n z z' (Fin.last n) (Matrix.of x)) ∂μ =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k n z) (Tz k n z') ζ) * ψ ζ)
    (hlaws : ∀ ψ : ℂ → ℝ≥0∞, Measurable ψ →
      ∫⁻ x, ψ (zetaL k ρ zs zs' (Fin.last ρ) (Matrix.of x)) ∂μs =
        ∫⁻ ζ, ENNReal.ofReal (B2.zWeight k (Tz k ρ zs) (Tz k ρ zs') ζ) * ψ ζ)
    (t : ℂ) (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn l)) (D.castM hn.symm (ιLev k 1 ρ g))) ∧
      (∀ l : Fin ρ, Rel T (L.p ⟨l.val + 1, by omega⟩) (Ls.p l) ∧ Rel T (L.c ⟨l.val + 1, by omega⟩) (Ls.c l) ∧
        Rel T (L.ci ⟨l.val + 1, by omega⟩) (Ls.ci l)) ∧
      (∀ (m : ℕ) (hm : m ≤ ρ) (Y : ℂ),
        MRel T (P5.QQi L st ⟨m + 1, by omega⟩ Y) (P5.QQi Ls sts ⟨m, by omega⟩ Y)) ∧
      ∀ Φ Ψ c, P5.pairAt μs (T Φ) (T Ψ) c = P5.pairAt μ Φ Ψ (fun l => consC t c (Fin.cast hn l)) := by
  subst hn
  rw [P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k 1 ρ y) := funext fun y => by rw [hπ, P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k 1 ρ y) := funext fun y => by rw [hπ', P.JCTx5.castM_rfl]
  rw [tz_iota, tz_iota] at hlaw
  have hmap : μs.map (B2.levM k ρ) = μ := map_levM_eq hμ hμs _ (zWeight_fin _ _) hlaw hlaws
  refine ⟨trL ht zs zs' π π', fun Φ c g => ?_, fun l => site_ops ht hL hLs l,
    fun m hm Y => qqi_rel_n ht hzs hzs' hL hLs hst hsts m hm Y, fun Φ Ψ c => ?_⟩
  · rw [P.JCTx5.castM_rfl]; rfl
  · exact pairAt_tr ht hmap Φ Ψ c

end Formalism.FourierDecayAlt.P.PTieL

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveLocalBuiltPlaces
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockKWave
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem prod_ofFn_map {K : ℕ} (f : Fin K → ℝ) (g : ℝ → ℝ) : ((List.ofFn f).map g).prod = ∏ b, g (f b) := by
  rw [List.map_ofFn, List.prod_ofFn]; rfl

section blockK

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem sW_eq (S : C.HidaSetting E Wp Wq) (j : ℕ) (l : ℂ) :
    sW S j l = Complex.I * (((2 * Real.pi / ((S.g : ℝ) * lamS S j)) : ℝ) : ℂ) * l := rfl

end blockK

end

end Formalism.FourierDecayAlt.P.PBL
end

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section wave

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def Xw (S : C.HidaSetting E Wp Wq) (i : ℕ) (v : Fin S.f) : ℝ :=
  (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r i 0)) * Real.exp 1 * (28 * S.G.N / S.G.lenI) ^ (2 * (i - 1) + 0) *
    J.supA S.G S.de S.de' S.T S.T' S.l (decide (i = 1 ∧ 0 + 1 = 1)) (S.pl v)

theorem g_cast (S : C.HidaSetting E Wp Wq) : ((S.g : ℕ) : ℝ) = S.G.g := by
  unfold C.HidaSetting.g Sz.Glob.g; push_cast; rfl

theorem len_eq (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem T_eq (S : C.HidaSetting E Wp Wq) (hg : 0 < S.G.g) (j : ℕ) :
    ((S.g : ℝ) * lamS S j) / (2 * Real.pi) = (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r (j + 1) 0)) := by
  unfold lamS
  rw [g_cast]
  have hx : 0 < S.G.g / (2 * Real.pi) := by positivity
  have e1 : 2 * Real.pi / S.G.g = (S.G.g / (2 * Real.pi))⁻¹ := by rw [inv_div]
  have key : ∀ n0 n1 : ℤ, n0 = n1 + 1 →
      S.G.g * (S.G.g / (2 * Real.pi)) ^ n1 / (2 * Real.pi) = (2 * Real.pi / S.G.g) ^ (-n0) := by
    intro n0 n1 h
    rw [h, e1, inv_zpow, zpow_neg, inv_inv, zpow_add_one₀ hx.ne']
    field_simp
  exact key _ _ (by unfold S6.nuBlock; push_cast; ring)

end wave

section main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem glob_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hB.1 hB.2.1, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; have := PBD.rd_pos' E; positivity

theorem lenI_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) : 0 < S.G.lenI := by
  have hGo := hB.2.2.2.2.2.2.2.2.2.2.1
  have h := (hGo v).1
  rw [len_eq] at h
  have : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by have := PBD.ntop_ge S; positivity
  linarith

theorem xw_nonneg (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (i : ℕ) (v : Fin S.f) : 0 ≤ Xw S i v := by
  obtain ⟨hg, hk⟩ := glob_pos hB
  have hl := lenI_pos hB v
  have hN : (0 : ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hA := supA_nonneg S hg hk v (decide (i = 1 ∧ 0 + 1 = 1))
  unfold Xw
  have : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

theorem thr_wave (hCc : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) :
    JC.HidaCurvatureBarriers S (fun i v => Xw S i v) := by
  intro i hi1 _ v
  obtain ⟨hg, hk⟩ := glob_pos hB
  have hl := lenI_pos hB v
  have hCA : Cc ≤ S.CA := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hN : (0:ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hcg : (0:ℝ) ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (i - 1) + 0) := by positivity
  have h := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hl
    (hCc.trans hCA) (fun one => supA_nonneg S hg hk v one)).1 i 0 (Real.exp 1) ((28 * S.G.N / S.G.lenI) ^ (2 * (i - 1) + 0))
    hi1 (Real.exp_pos 1).le le_rfl hcg le_rfl
  refine ⟨xw_nonneg hB i v, ?_⟩
  show Xw S i v ≤ J.thrS S.G S.CA S.de S.de' S.T S.T' S.l i 1 (S.pl v)
  unfold Xw
  exact_mod_cast h

end main

section main2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem xw_K (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (j K : ℕ) (grid : Fin K → Fin (2 * j + 1) → ℝ)
    (hl1 : ∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * j)) :
    (∏ b, ∑ i, |F7.lagCo (grid b) i|) * (((S.g : ℝ) * lamS S j) / (2 * Real.pi)) ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v)) ^ K ≤ (Xw S (j + 1) v) ^ K := by
  obtain ⟨hg, hk⟩ := glob_pos hB
  have hl := lenI_pos hB v
  rw [T_eq S hg j]
  have hdec : decide (j + 1 = 1 ∧ 0 + 1 = 1) = decide (j = 0) := by
    by_cases h : j = 0 <;> simp [h]
  have hexp : 2 * (j + 1 - 1) + 0 = 2 * j := by omega
  unfold Xw
  rw [hdec, hexp]
  rw [ntop_eq_N', len_eq] at hl1
  set cg := (28 * S.G.N / S.G.lenI) ^ (2 * j) with hcg
  set Tf := (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r (j + 1) 0)) with hTf
  set A := J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v) with hA
  have hA0 : 0 ≤ A := supA_nonneg S hg hk v _
  have hgg : 0 < 2 * Real.pi / S.G.g := by positivity
  have hTf0 : 0 ≤ Tf := by positivity
  have hprod : (∏ b, ∑ i, |F7.lagCo (grid b) i|) ≤ cg ^ K := by
    calc (∏ b, ∑ i, |F7.lagCo (grid b) i|) ≤ ∏ _b : Fin K, cg :=
          Finset.prod_le_prod₀ (fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun b _ => hl1 b
      _ = cg ^ K := by simp
  have h1 : 0 ≤ Tf ^ K * (Real.exp 1 * A) ^ K := by positivity
  calc (∏ b, ∑ i, |F7.lagCo (grid b) i|) * Tf ^ K * (Real.exp 1 * A) ^ K
      = (∏ b, ∑ i, |F7.lagCo (grid b) i|) * (Tf ^ K * (Real.exp 1 * A) ^ K) := by ring
    _ ≤ cg ^ K * (Tf ^ K * (Real.exp 1 * A) ^ K) := mul_le_mul_of_nonneg_right hprod h1
    _ = (Tf * Real.exp 1 * cg * A) ^ K := by ring

end main2

end

end Formalism.FourierDecayAlt.P.PBL
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHAsm
open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem fsv_zero' (t : ℂ) : fsv 0 t = 1 := by simp [fsv]

theorem fsv_mul' (s s' t : ℂ) : fsv s t * fsv s' t = fsv (s + s') t := by
  unfold fsv
  rw [← Complex.exp_add]
  congr 1
  simp only [map_add (f := _)]
  ring

theorem fsv_contDiff' (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hc : ContDiff ℝ ∞ (fun t : ℂ => conj t) := Complex.conjCLE.contDiff
  have h1 : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul hc)
  have he : ContDiff ℝ ∞ Complex.exp := Complex.contDiff_exp
  exact he.comp h1

section asm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem cc_zero {P : M.Par} (j : ℕ) (hj : j + 1 ≤ P.r) (t : ℂ) (c : Fin (P.r - (j + 1)) → ℂ) :
    cc j hj t c ⟨0, by omega⟩ = t := by
  simp [cc, consC]

theorem vw_entry (hU : UUiwScalar) {V : Type} [AddCommGroup V] [Module ℂ V] (S : Type) [Fintype S] [DecidableEq S]
    (Wv Wv' : Module.End ℂ V) (s : ℂ) (w : List (Wd.Letter ℂ S)) (a b : Wd.Ix S) :
    ∃ lam : ℂ, ∀ Φ : V, (Wd.Vw (mkP Wv Wv') s w a b).1 Φ = lam • Wv Φ := by
  obtain ⟨lam, hlam⟩ := Algebra.mem_bot.1 (hU (Pr V) S s w a b)
  refine ⟨lam, fun Φ => ?_⟩
  have hab : Wd.Vw (mkP Wv Wv') s w a b = mkP Wv Wv' * Wd.UUiw (A := Pr V) s w a b := by
    simp [Wd.Vw, Wd.io, Matrix.scalar_apply, Matrix.diagonal_mul]
  rw [hab, ← hlam]
  change (Wv * algebraMap ℂ (Module.End ℂ V) lam) Φ = _
  rw [Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]

theorem class0_form (hU : UUiwScalar) (S : Type) [Fintype S] [DecidableEq S] (P : M.Par)
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (hj : j + 1 ≤ P.r)
    (Lj : R.LevelData (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (P.r - j))
    (stj : Fr.Start (Pr (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))) (l0 : ℕ) :
    ∀ (i : Fin ((JC.parLev P j).r + 1))
      (Ψ : RadSp (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      HerGenC S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) i Ψ → i = 0 →
      ∃ (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
        (Φ : RadSp (JC.parLev P j).k (JC.parLev P j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (s κ : ℂ),
        JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F ∧
        IsRadJF (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' (T.bs j) F Φ ∧
        ∀ c g, (Ψ : Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp)) c g =
          (κ * fsv s (c ⟨0, by change 0 < P.r - j; omega⟩)) •
            (Φ : Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp)) c g := by
  intro i Ψ h
  induction h with
  | jf F Φ hF hΦ =>
    intro _
    exact ⟨F, Φ, 0, 1, hF, hΦ, fun c g => by simp [fsv_zero']⟩
  | slice l w a b Φ hw hΦ ih =>
    intro h
    exact absurd h (Fin.succ_ne_zero l)
  | waveC l w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
    intro h
    have hl0 : l.val = 0 := by
      have := congrArg Fin.val h
      simpa using this
    obtain ⟨F, Φ0, s0, κ0, hF, hΦ0, hv⟩ := ih h
    obtain ⟨lam, hlam⟩ := vw_entry hU S Wv Wv' s w a b
    refine ⟨F, Φ0, s + s0, lam * κ0, hF, hΦ0, fun c g => ?_⟩
    have hcl : c l = c ⟨0, by change 0 < P.r - j; omega⟩ := congrArg c (Fin.ext hl0)
    rw [hlam, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hW, hv, smul_smul, smul_smul]
    beta_reduce
    rw [hcl, ← fsv_mul']
    congr 1
    ring
  | waveZ w s Wv Wv' a b Φ hw hW hW' hΦ ih =>
    intro h
    have := congrArg Fin.val h
    simp [JC.parLev] at this
    omega

variable {P : M.Par} {T : D.LevTower P.k P.r Wp Wq} {j : ℕ} {hj : j + 1 ≤ P.r}

theorem inC_add (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ Ψ' : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    (h : InC T j hj Ψ) (h' : InC T j hj Ψ') : InC T j hj (Ψ + Ψ') := by
  obtain ⟨G, hG, hR⟩ := h
  obtain ⟨G', hG', hR'⟩ := h'
  refine ⟨fun t γ => G t γ + G' t γ, (h2 Wp Wq P T j G G' hG hG' (fun _ => 1) contDiffOn_const).1,
    fun t ht x hx => ?_⟩
  rw [Submodule.coe_add, Pi.add_apply, Pi.add_apply, hR t ht x hx, hR' t ht x hx,
    (h4 Wp Wq P T hP hT j hj hPs G G' hG hG' t ht 0 x hx).1]

theorem inC_smul (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    (h : InC T j hj Ψ) (a : ℂ) : InC T j hj (a • Ψ) := by
  obtain ⟨G, hG, hR⟩ := h
  refine ⟨fun t γ => a • G t γ, (h2 Wp Wq P T j G G hG hG (fun _ => a) contDiffOn_const).2,
    fun t ht x hx => ?_⟩
  rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hR t ht x hx,
    (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht a x hx).2]

theorem inC_seed (h6 : CellTie) (h7 : SliceFamGood) (h8 : SliceFamJF)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (hF : JFOKCpt (JC.parLev P j) (T.bs j).z (T.bs j).z' F)
    (Φ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsRadJF (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' (T.bs j) F Φ) :
    InC T j hj Φ := by
  refine ⟨sliceFam T j hj F, h7 Wp Wq P T hP hT j hj hPj hPs F hF, fun t ht x hx => ?_⟩
  obtain ⟨hdom, hGV, hOm⟩ := h6 Wp Wq P T hP hT j hj hPj hPs t ht x hx
  have e1 : (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) (cc j hj t x.1) (gi j hj x.2) =
      resG P.k (P.r - j) (Fin.last _) (B.JF (T.bs j) F) (cc j hj t x.1) (gi j hj x.2) :=
    hΦ (cc j hj t x.1, gi j hj x.2) hdom
  have e2 := Formalism.FourierDecayAlt.P.PBP.resG_cast (k := P.k) (ρ := P.r - (j + 1)) (n := P.r - j) (by omega) ht
    (B.JF (T.bs j) F) x.1 x.2
  rw [e1]
  refine e2.trans ?_
  unfold resG
  rw [h8 Wp Wq P T hP hT j hj hPj hPs F hF t ht _ hGV hOm, smul_comm]
  congr 2

theorem inC_wave (h2 : FamAlg) (h4 : RepLin) (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π')
    (hT : D.TowerNormalised T)
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    {Φ Ψ : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'} (s κ : ℂ)
    (hv : ∀ c g, (Ψ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c g =
      (κ * fsv s (c ⟨0, by omega⟩)) • (Φ : Fn P.k (P.r - j) (Wq →L[ℂ] Wp)) c g)
    (h : InC T j hj Φ) : InC T j hj Ψ := by
  obtain ⟨G, hG, hR⟩ := h
  have hm : ContDiffOn ℝ ∞ (fun t : ℂ => κ * fsv s t) {t | t ≠ 0} :=
    (contDiff_const.mul (fsv_contDiff' s)).contDiffOn
  refine ⟨fun t γ => (κ * fsv s t) • G t γ, (h2 Wp Wq P T j G G hG hG _ hm).2, fun t ht x hx => ?_⟩
  rw [hv, cc_zero, hR t ht x hx, (h4 Wp Wq P T hP hT j hj hPs G G hG hG t ht _ x hx).2]

theorem inC_adjoin (h2 : FamAlg) (h4 : RepLin) (h9 : OpClosed)
    (hP : IsPlace P T.base.z T.base.z' T.base.π T.base.π') (hT : D.TowerNormalised T)
    (hPj : IsPlace (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hPs : IsPlace (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (X : ActualOps P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (A : Module.End ℂ (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
    (hA : A ∈ Algebra.adjoin ℂ (Set.range (X.op ⟨0, by omega⟩))) :
    ∀ Ψ, InC T j hj Ψ → InC T j hj (A Ψ) := by
  induction hA using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact fun Ψ h => h9 Wp Wq P T hP hT j hj hPj hPs X i Ψ h
  | algebraMap r =>
    intro Ψ h
    rw [Module.algebraMap_end_apply]
    exact inC_smul h2 h4 hP hT hPs h r
  | add x y _ _ hx hy =>
    intro Ψ h
    rw [LinearMap.add_apply]
    exact inC_add h2 h4 hP hT hPs (hx Ψ h) (hy Ψ h)
  | mul x y _ _ hx hy =>
    intro Ψ h
    rw [Module.End.mul_apply]
    exact hx _ (hy Ψ h)

theorem herKc_jf' {S : Type} [Fintype S] [DecidableEq S] {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ}
    {π : Mx P.k P.r → (Wp →L[ℂ] Wp)} {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}
    {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
    {D : B.RealPlaceData P.k P.r Wp Wq} (F : Mx P.k P.r → (Wq →L[ℂ] Wp)) (hF : JFOKCpt P z z' F)
    (Φ : RadSp P.k P.r z z' π π') (hΦ : IsRadJF P z z' π π' D F Φ) : Φ ∈ herKc S P z z' π π' L st l0 D 0 :=
  Submodule.subset_span (HerGenC.jf F Φ hF hΦ)

theorem span_step
    (Tt : RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' →ₗ[ℂ]
      RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π')
    (A : Module.End ℂ (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
    (K : Submodule ℂ (RadSp P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π'))
    (s : Set (RadSp P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) (hgen : ∀ Ψ ∈ s, Tt (A Ψ) ∈ K) :
    ∀ Ψ ∈ Submodule.span ℂ s, Tt (A Ψ) ∈ K := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _)]; exact K.add_mem hx hy
  | smul r x _ hx => rw [map_smul, map_smul]; exact K.smul_mem r hx

end asm

theorem sliceStepHer_of (h1 : FamJFOK) (h2 : FamAlg) (h4 : RepLin) (h6 : CellTie) (h7 : SliceFamGood)
    (h8 : SliceFamJF) (h9 : OpClosed) (h10 : BTlAdjoin) (h11 : UUiwScalar) : PTie.SliceStepHer := by
  intro Wp Wq _ _ _ _ _ _ P T hP hT j hj l0 _ _ Xj μj Lj stj Xs μs Ls sts hDj hDs Tt t ht hTt S _ _ w a b hw Ψ hΨ
  have hPj := hDj.1
  have hPs := hDs.1
  have hAct := hDj.2.2.1
  have hA := h10 Wp Wq P.k (P.r - j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Xj Lj hAct S
    ⟨0, by change 0 < P.r - j; omega⟩ w a b
  have hΨ' : Ψ ∈ Submodule.span ℂ
      {Φ | HerGenC S (JC.parLev P j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' Lj stj l0 (T.bs j) 0 Φ} := hΨ
  refine span_step (P := P) (T := T) (j := j) Tt (bTl Lj ⟨0, by change 0 < P.r - j; omega⟩ w a b).1
    (herKc S (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π' Ls sts
      l0 (T.bs (j + 1)) 0) _ (fun Ψ hg => ?_) Ψ hΨ'
  obtain ⟨F, Φ, s, κ, hF, hΦ, hv⟩ := class0_form h11 S P T j hj Lj stj l0 0 Ψ hg rfl
  have hC0 : InC T j hj Φ := inC_seed h6 h7 h8 hP hT hPj hPs F hF Φ hΦ
  have hC : InC T j hj Ψ := inC_wave (Φ := Φ) h2 h4 hP hT hPs s κ hv hC0
  obtain ⟨G, hG, hR⟩ := inC_adjoin h2 h4 h9 hP hT hPj hPs Xj _ hA Ψ hC
  have hJ := h1 Wp Wq P T j G hG t ht
  have hRad : IsRadJF (JC.parLev P (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' (T.bs (j + 1)).π (T.bs (j + 1)).π'
      (T.bs (j + 1)) (G t) (Tt ((bTl Lj ⟨0, by change 0 < P.r - j; omega⟩ w a b).1 Ψ)) := fun x hx =>
    (hTt _ x.1 x.2).trans (hR t ht x hx)
  exact herKc_jf' (S := S) (P := JC.parLev P (j + 1)) (L := Ls) (st := sts) (l0 := l0) (G t) hJ _ hRad

end Formalism.FourierDecayAlt.P.CutSH

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
end
end
