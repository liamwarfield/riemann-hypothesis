module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaCutoffLimit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
namespace Formalism.FourierDecayAlt.P.TLB

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
  Formalism.YangianSpanCharacter.T

noncomputable section

section gen

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

theorem tprod_take_all (L : LevelData A r) (Y : ℂ) :
    L.Tprod Y = ((List.ofFn (L.Tl Y)).take r).reverse.prod := by
  unfold LevelData.Tprod
  rw [List.take_of_length_le (by simp)]

variable [StarRing A] [StarModule ℂ A]

theorem star_algMap (z : ℂ) : star (algebraMap ℂ A z) = algebraMap ℂ A (starRingEnd ℂ z) := by
  rw [← algebraMap_star_comm]; rfl

theorem star_Tl_gen (L : LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (y : ℂ) (l : Fin r) :
    (L.Tl y l)ᴴ = (L.Tvl (starRingEnd ℂ y) l)ᵀ := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tl, LevelData.Tvl, conjTranspose_apply, star_add, star_neg, hp, hc, hci, star_algMap,
      sub_eq_add_neg]

theorem star_Tprod_gen (L : LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (y : ℂ) :
    (L.Tprod y)ᴴ = (L.Tvprod (starRingEnd ℂ y))ᵀ := by
  rw [Formalism.FourierDecayAlt.P.MAx3.Q.Tvprod_transpose]
  unfold LevelData.Tprod
  rw [conjTranspose_list_prod, List.map_reverse, List.reverse_reverse, List.map_ofFn]
  congr 1
  exact congrArg List.ofFn (funext fun l => star_Tl_gen L hp hc hci y l)

end gen

section actual

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rma_pref_take (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) :
    ∀ n, Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n = ((List.ofFn (L.Tl Y)).take n).reverse.prod
  | 0 => by simp [Formalism.FourierDecayAlt.P.JCx2.rma_pref]
  | n + 1 => by
    by_cases h : n < r
    · rw [Formalism.FourierDecayAlt.P.JCx2.rma_pref, dite_eq_left h, rma_pref_take L Y n, List.take_add_one, List.reverse_append,
        List.prod_append]
      have e : (List.ofFn (L.Tl Y))[n]? = some (L.Tl Y ⟨n, h⟩) := by simp [h]
      rw [e]
      simp only [Option.toList_some, List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons,
        List.prod_nil, mul_one]
      congr 1
    · rw [Formalism.FourierDecayAlt.P.JCx2.rma_pref, dite_eq_right h, rma_pref_take L Y n, List.take_of_length_le (by simp; omega),
        List.take_of_length_le (by simp; omega)]

theorem tprod_zero_eq (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) : tprod L Y 0 = L.Tprod Y := by
  have h : tprod L Y 0 = Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y r := by
    have := Formalism.FourierDecayAlt.P.JCx2.rma_tprod_pref L Y r 0 (by omega)
    simpa [Formalism.FourierDecayAlt.P.JCx2.rma_pref] using this
  rw [h, rma_pref_take, tprod_take_all]

end actual

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

noncomputable section

theorem actual_algebra_facts : TL.ActualAlg := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  have hD' := hD
  obtain ⟨hpl, -, hL, hQQ, -, -, hSL, hst⟩ := hD
  obtain ⟨sp, sc, sci⟩ := P5.HerA.star_site_ops hL
  have hcent : ∀ (l : Fin P.r) (Y : ℂ) (a b : Fin 2),
      st.QQ Y a b ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
    intro l Y a b
    obtain ⟨hp, -, hc, hci, -⟩ := hL
    have ht : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * X.op l i = X.op l i * X.t Y a b :=
      fun i => (Formalism.FourierDecayAlt.P.level_coordinates_commute Wp Wq P z z' π π' hpl X l i).1
    have htn : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * -X.op l i = -X.op l i * X.t Y a b := by
      intro i Y a b; rw [mul_neg, neg_mul, ht]
    rw [hQQ Y, Matrix.smul_apply]
    refine SMulMemClass.smul_mem _ ?_
    simp only [ActualOps.QQ, Matrix.of_apply]
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    simp only [hol, site, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [hp l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (htn _ _ _ _), P5.HerA.pair_operator_commute (htn _ _ _ _).symm (ht _ _ _ _)⟩
    · rw [hc l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
    · rw [hci l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
  have hqq : ∀ Y i j, ∀ x ∈ siteOps L, Commute (st.QQ Y i j) x := by
    intro Y i j x hx
    have key := fun l => (StarSubalgebra.mem_centralizer_iff ℂ).1 (hcent l Y i j)
    simp only [siteOps, Set.mem_union, Set.mem_range] at hx
    rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
    · have h := key l
      exact (h (L.p l) (by simp [hol, site])).1.symm
    · have h2 := (key l (L.p l) (by simp [hol, site])).2
      rw [sp l] at h2
      exact Commute.neg_right_iff.1 (show Commute (st.QQ Y i j) (-L.pb l) from h2.symm)
    · exact (key l (L.c l) (by simp [hol, site])).1.symm
    · exact (key l (L.ci l) (by simp [hol, site])).1.symm
    · have h2 := (key l (L.c l) (by simp [hol, site])).2
      rw [sc l] at h2
      exact h2.symm
    · have h2 := (key l (L.ci l) (by simp [hol, site])).2
      rw [sci l] at h2
      exact h2.symm
  refine ⟨⟨hSL, hst, sp, sc, sci, hqq⟩, fun Y hY => ?_, fun Y hY => ?_⟩
  · have hY' : starRingEnd ℂ Y = Y := hY
    unfold P5.QQi
    simp only [Fin.val_zero]
    rw [hY, TLB.tprod_zero_eq, TLB.star_Tprod_gen L sp sc sci, hY']
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, cst, nP, LevelData.Ar, LevelData.Br,
      LevelData.Avr, LevelData.Bvr]
    simp only [add_mul, mul_add, mul_assoc]
    abel
  · obtain ⟨κ, hx, hxi, -⟩ :=
      P5.xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual P5.kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD'
    classical
    set f : M.Ty P → ℂ := fun ρ => M.x0 P l0 ρ Y with hf
    set N : Finset ℂ := Finset.univ.image f
    set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)
    have hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹ := by
      intro ρ
      have hmem : f ρ ∈ N := Finset.mem_image_of_mem _ (Finset.mem_univ ρ)
      have h := Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem
      simpa only [id] using h
    have he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p := by
      funext ρ
      rw [← hp ρ]
      have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : M.Ty P => ℂ) ρ) f p
      rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at this
      rw [this]
      rfl
    refine ⟨p, ?_⟩
    rw [hxi Y hY, hx Y, Polynomial.aeval_algHom_apply]
    exact congrArg κ he

end

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

def JfFF (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  ∀ v, B.JF (T v).base (f v) ∈
    Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

end defs

def JfSmoothDS : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → JfFF S T f

def ModelPlaceBuilt3 : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ → JfFF S T f → (∀ v, (S.G.place (S.pl v)).Ok) →
    Sz.IsWord S.G.k S.de → Sz.IsWord S.G.k S.de' → ∀ c : LE.Cut, c.χ = χ → ∀ v : Fin S.f,
      ∃ (L : R.LevelData (MA.A (D.parOf S v) (MA.DQ (D.parOf S v))) (D.parOf S v).r)
        (j : M.Ty (D.parOf S v) → MA.SmQ (D.parOf S v).r (D.parOf S v).TT)
        (lam : Fin ((D.parOf S v).k + 2 * (D.parOf S v).r + 1) → ℝ) (Cm σ : ℝ),
        JC.IsModelPlace S T f χ v L j lam c Cm σ

def RegFF3 : Prop :=
  ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → JfFF S T f →
    ∀ v, B.JF (T v).base (f v) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v) ∧ ∀ ε : ℝ, 0 < ε → B.JF (T v).base (D.cutF (T v).base χ (f v) ε) ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)

section proofs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem gf_SgS (Bs : B.RealPlaceData k r Wp Wq) {s s' : Q.Mx k r} (hs : s ∈ Sset k r Bs.z) (hs' : s' ∈ Sset k r Bs.z')
    (g : Q.Mx k r) : Gf k r Bs.z Bs.z' (s * g * s') = Gf k r Bs.z Bs.z' g := by
  unfold Gf
  rw [dInv k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem s hs s' hs' g,
    dInv k r Bs.z Bs.z' Bs.z_mem Bs.z'_mem s hs s' hs' g]

theorem one_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) : (1 : Q.Mx k r) ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, (nSubgroup k r).1, by simp⟩

theorem n_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {n : Q.Mx k r} (hn : n ∈ Q.Nlev k r 0) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, n, hn.1, by simp⟩

theorem h_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {h : Q.Mx k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

theorem cut_mem_FFl (Bs : B.RealPlaceData k r Wp Wq) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ) (ε : ℝ)
    {Dm : Set (Q.Mx k r)} {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm) :
    (fun g => ((χ (Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • J g) ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 Dm := by
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    refine ⟨U, fun g => ((χ (Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ) • F g, hU, hgU, ?_, ?_⟩
    · have hc : ContDiff ℝ (⊤ : ℕ∞) (fun g : Q.Mx k r => ((χ (Gf k r Bs.z Bs.z' g / ε) : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (hχ.comp ((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Bs.z Bs.z').div_const ε))
      exact hc.contDiffOn.smul hF
    · intro g hgU hgG
      simp only [hFJ g hgU hgG]
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

end proofs

theorem regularity_smooth_forms_holds : RegFF3 := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB hJ v
  refine ⟨hJ v, fun ε _ => ?_⟩
  have hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := hB.1.2.2.2.1.1.1
  have e : B.JF (T v).base (D.cutF (T v).base χ (f v) ε) =
      fun g => ((χ (Gf S.G.k S.G.r (T v).base.z (T v).base.z' g / ε) : ℝ) : ℂ) • B.JF (T v).base (f v) g :=
    funext fun g => Formalism.FourierDecayAlt.P.JCTx2.JF_cutF (T v).base χ (f v) ε g
  rw [e]
  exact cut_mem_FFl (T v).base hχ ε (hJ v)

section bridge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem isBuiltPlace_mono3 {Cc₁ Cc₂ : ℝ} (h : Cc₁ ≤ Cc₂) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ}
    {ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ} {m₀ : Fin S.f → B.Mat S.G.k S.G.r}
    {top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ}
    {A₀ : ℝ} (hB : JCT.IsBuiltPlace Cc₂ S T f χ ν' m₀ top A₀) : JCT.IsBuiltPlace Cc₁ S T f χ ν' m₀ top A₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hB
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, le_trans h h9, h10, h11, ?_, h13⟩
  · intro v
    have hv := h8 v
    have hX : 0 ≤ (S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2 +
        (S.Ntop : ℝ) ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h hX]
  · have hX : 0 ≤ ((S.G.r : ℝ) + 1) ^ 4 *
        ((S.Ntop : ℝ) * (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 2 + (2 * (S.G.r : ℝ) + S.G.k + 1) ^ 3) := by positivity
    have := mul_le_mul_of_nonneg_right h hX
    nlinarith

end bridge

theorem modelPlaceBuilt2_of_3 (hJ : JfSmoothDS) (h3 : ModelPlaceBuilt3) : JCT.ModelPlaceBuilt2 := by
  obtain ⟨C₁, hC₁⟩ := hJ
  obtain ⟨C₂, hC₂⟩ := h3
  refine ⟨max C₁ C₂, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB
  exact hC₂ E Wp Wq S T f χ ν' m₀ top A₀ (isBuiltPlace_mono3 (le_max_right _ _) hB)
    (hC₁ E Wp Wq S T f χ ν' m₀ top A₀ (isBuiltPlace_mono3 (le_max_left _ _) hB))

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_JA_LocLemmas
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

def CoefG {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (d Bg : ℝ) : Prop :=
  ∀ Tm ∈ Θ, ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat k r),
    (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
      ‖B.dLR u w Tm.coef g‖ ≤ Cb * B.gN g ^ (d + Bg * m) ∧ ‖B.dLR u w Tm.coefAdj g‖ ≤ Cb * B.gN g ^ (d + Bg * m)

def OpCCg : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (d Bg A η : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    0 < η → 0 ≤ Bg → B.SmoothCoef (B.GPos Bs) Θ → CoefG Bs Θ d Bg →
    B.CkOn ⊤ (B.GV k r) F → (∀ m : ℕ, B.InCC (A - Bg * m) m F) →
    (∀ g ∈ B.GV k r, Gf k r Bs.z Bs.z' g < η → F g = 0) →
    (B.CkOn ⊤ (B.GV k r) (B.opApply Θ F) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (B.opApply Θ F)) ∧
    (B.CkOn ⊤ (B.GV k r) (B.opAdj Θ F) ∧
      ∀ m : ℕ, B.InCC (A - d - Bg * (B.opOrder Θ : ℝ) - Bg * m) m (B.opAdj Θ F))

def AgreeOm : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (J F : B.Mat k r → (Wq →L[ℂ] Wp)) (U : Set ℝ),
    J ∈ Q.FFl k r Bs.z Bs.z' Bs.π Bs.π' 0 {g | 0 < Gf k r Bs.z Bs.z' g ∧
      ∀ a : Fin r, Dmin k r Bs.z Bs.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} →
    (∀ q ∈ JF.QDom k r Bs.z Bs.z', Gf k r Bs.z Bs.z' (B.gq Bs q) ∈ U → J (B.gq Bs q) = B.JF Bs F (B.gq Bs q)) →
    ∀ g ∈ JF.Om k r Bs.z Bs.z', Gf k r Bs.z Bs.z' g ∈ U → J g = B.JF Bs F g

def ThetaJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (UU : Set (B.Mat k r)),
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A (B.opOrder Θ) → B.SmoothCoef (B.GPos Bs) Θ → B.Commutes Bs (B.GPos Bs) Θ →
    B.CkOn ⊤ (B.GV k r) F → B.InCC A (B.opOrder Θ) F →
    UU ⊆ JF.Om k r Bs.z Bs.z' → B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF Bs F) →
    (∀ g ∈ JF.Om k r Bs.z Bs.z', B.opApply Θ (B.JF Bs F) g = B.JF Bs (B.opApply Θ F) g) ∧
      ∀ g ∈ UU, B.opAdj Θ (B.JF Bs F) g = B.JF Bs (B.opAdj Θ F) g

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

namespace Formalism.FourierDecayAlt.P.CutMP.JA.LT

def ThetaJApply : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (Θ : B.DiffOp k r Wp Wq) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A (B.opOrder Θ) → B.SmoothCoef (B.GPos Bs) Θ → B.Commutes Bs (B.GPos Bs) Θ →
    B.CkOn ⊤ (B.GV k r) F → B.InCC A (B.opOrder Θ) F →
    ∀ g ∈ JF.Om k r Bs.z Bs.z', B.opApply Θ (B.JF Bs F) g = B.JF Bs (B.opApply Θ F) g

end Formalism.FourierDecayAlt.P.CutMP.JA.LT

end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRad
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsNv (l : Fin (r + 1)) (s : Fin (k + 1)) : Fin (r - l.val + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < s.val then r + j.val else r + j.val + 1, by
    have := j.isLt; have := s.isLt; have := l.isLt; split_ifs <;> omega⟩

def NLv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
    (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (g *ᵥ bvec (wI k r s)) z * z' (wI k r t)) •
      qminorOp (Q.EH k r) (rowsNv k r l s) (rowsNv k r l t) u f g

def FNv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (J : Q.Mx k r → E) (l : Fin (r + 1)) : Q.Fn k r E :=
  Q.resG k r (Fin.last r) (NLv k r z z' l (Q.uC k r (Fin.last r) Y - 1) J)

end defs

def JDRvBeta : Prop :=
  ∀ k r : ℕ, ∃ σ : ℂ, σ ≠ 0 ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (Y : ℂ) (f : Q.Mx k r → E), inWb k r z → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      rvhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
        (σ * ∏ a, c a) • NLv k r z z' 0 (Q.uC k r (Fin.last r) Y - 1) f (Q.wCell k r (Fin.last r) c * g)

def JDRvTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J (Fin.last r) c g = -Q.QL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J) c g

def JDRvStepA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J ⟨r - 1, by omega⟩ c g =
        (Y • FNv k r z z' Y J (Fin.last r) - Q.crd (Formalism.QuantumDeterminants.pbOp ⟨r - 1, by omega⟩) (FNv k r z z' Y J (Fin.last r)) -
          Q.crd (Formalism.QuantumDeterminants.cbiOp ⟨r - 1, by omega⟩) (Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J))) c g

def JDRvStepB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ (l : ℕ) (hl : l + 2 ≤ r),
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J ⟨l, by omega⟩ c g =
        (Y • FNv k r z z' Y J ⟨l + 1, by omega⟩ -
          Q.crd (Formalism.QuantumDeterminants.pbOp ⟨l, by omega⟩) (FNv k r z z' Y J ⟨l + 1, by omega⟩) -
          Q.crd (Formalism.QuantumDeterminants.cbOp ⟨l + 1, by omega⟩) (Q.crd (Formalism.QuantumDeterminants.cbiOp ⟨l, by omega⟩)
            (FNv k r z z' Y J ⟨l + 2, by omega⟩))) c g

def JDRvChainM : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FNv k r z z' Y J 0 c g =
        -(Q.QL k r z z' (Fin.last r) Y 0 1 (Q.crd (Q.cmp (Q.vABs r Y r) 0) (Q.resG k r (Fin.last r) J)) +
          Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (Q.cmp (Q.vABs r Y r) 1) (Q.resG k r (Fin.last r) J))) c g

def JDRvConseq : Prop := JDRvTop → JDRvStepA → JDRvStepB → JDRvChainM

theorem jDRRadM_of_parts (hB : JDRvBeta) (hT : JDRvTop) (hA : JDRvStepA) (hS : JDRvStepB) (hC : JDRvConseq) :
    JDRRadM := by
  have hCh := hC hT hA hS
  intro k r
  obtain ⟨σ, hσ, hβ⟩ := hB k r
  refine ⟨-σ⁻¹, ?_⟩
  intro Wp Wq _ _ _ _ z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have h1 := hβ (Wq →L[ℂ] Wp) z z' Y J hz c hc g hg
  have h2 := hCh Wp Wq k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  simp only [FNv, Q.resG] at h2
  simp only [Q.resG, rhvGrp, dMul, drF]
  rw [h1, smul_smul, smul_smul, show ∀ a b : ℂ, a * -σ⁻¹ * (σ * b) = -b * a from fun a b => by field_simp,
    ← smul_smul, h2, smul_neg, neg_smul, neg_neg]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff ComplexConjugate

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem toSm_val_of_mem (P : M.Par) {u : MA.Qp P.r P.TT → ℂ} (h : u ∈ MA.smSub P.r P.TT) :
    ((MA.toSm P u : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) = u := by
  unfold MA.toSm; rw [dite_eq_left h]

theorem hsVec_sum_smul {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {ι : Type} [Fintype ι] (c : ι → ℂ) (e : ι → (W →L[ℂ] V)) :
    B.hsVec (∑ ρ, c ρ • e ρ) = ∑ ρ, c ρ • B.hsVec (e ρ) := by
  change Formalism.FourierDecayAlt.P.JFxI.hsVecL (∑ ρ, c ρ • e ρ) = ∑ ρ, c ρ • Formalism.FourierDecayAlt.P.JFxI.hsVecL (e ρ)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul]

theorem parseval {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {ι : Type} [Fintype ι] (e : ι → (W →L[ℂ] V))
    (X Y : W →L[ℂ] V) (hX : X = ∑ ρ, inner ℂ (B.hsVec (e ρ)) (B.hsVec X) • e ρ) :
    inner ℂ (B.hsVec Y) (B.hsVec X) =
      ∑ ρ, inner ℂ (B.hsVec (e ρ)) (B.hsVec X) * conj (inner ℂ (B.hsVec (e ρ)) (B.hsVec Y)) := by
  conv_lhs => rw [hX]
  rw [hsVec_sum_smul, inner_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [inner_smul_right, inner_conj_symm]

theorem jgq_contDiffOn {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    {J : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))}
    (hJ : J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)) :
    ContDiffOn ℝ ∞ (fun x => J (B.gq (T v).base x)) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := by
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r Db.z Db.z' := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    have h3 : S.T * S.T' < Complex.normSq x.2 := hx.2
    rw [hT, hT']; exact h3
  have hGl : ∀ x ∈ JF.QDom S.G.k S.G.r Db.z Db.z', B.gq Db x ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v := fun x hx =>
    om_sub' (Formalism.FourierDecayAlt.P.big_cell_domain S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) Db x hx)
  have hgq : ContDiffOn ℝ ∞ (fun x => B.gq Db x) (JF.QDom S.G.k S.G.r Db.z Db.z') :=
    contDiffOn_infty.2 fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn Db n
  refine contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => ?_
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hJ.1 _ (hGl x₀ (hQ x₀ hx₀))
  refine ⟨JF.QDom S.G.k S.G.r Db.z Db.z' ∩ (fun x => B.gq Db x) ⁻¹' U,
    hgq.continuousOn.isOpen_inter_preimage (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open _ _) hU, ⟨hQ x₀ hx₀, hgU⟩, ?_⟩
  have hc : ContDiffOn ℝ ∞ (fun x => F (B.gq Db x))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT ∩ (JF.QDom S.G.k S.G.r Db.z Db.z' ∩ (fun x => B.gq Db x) ⁻¹' U)) :=
    hF.comp (hgq.mono fun x hx => hx.2.1) fun x hx => hx.2.2
  exact hc.congr fun x hx => hJF _ hx.2.2 (hGl x hx.2.1).1

theorem beta_frame_identity_holds : BetaFrame := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hplace e hFr J₁ hJ₁ J₂ hJ₂ hN₁ hN₂
  set Db := (T v).base with hDb
  have hT : Tz S.G.k S.G.r Db.z = S.T := hplace.2.2.2.1
  have hT' : Tz S.G.k S.G.r Db.z' = S.T' := hplace.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' = (D.parOf S v).TT := by rw [hT, hT']; rfl
  set Qs := MA.Qset (D.parOf S v).r (D.parOf S v).TT with hQs
  have hQm : MeasurableSet Qs := (MA.Qset_open _ _).measurableSet
  set W : (Fin S.G.r → ℂ) × ℂ → ℝ := bcWeight S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') with hWdef
  have hW0 : ∀ x, 0 ≤ W x := fun x => Formalism.FourierDecayAlt.P.JCTx2.bcWeight_nonneg' _ _ x

  have hW : ∀ x ∈ Qs, W x = Formalism.FourierDecayAlt.P.MAx2.Adj.dR x * MA.wq S.G.k x (D.parOf S v).TT := by
    intro x hx
    have hle : Tz S.G.k S.G.r Db.z * Tz S.G.k S.G.r Db.z' ≤ Complex.normSq x.2 := by
      rw [hTT]; exact le_of_lt hx.2
    rw [hWdef]
    unfold bcWeight
    rw [if_pos hle]
    unfold Formalism.FourierDecayAlt.P.MAx2.Adj.dR MA.wq
    rw [hTT, ← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    have hM : 2 ≤ MA.Mdim S.G.k S.G.r l := by
      have := l.isLt
      simp only [MA.Mdim]; omega
    have hn : Complex.normSq (x.1 l) ≠ 0 := (Complex.normSq_pos.2 (hx.1 l)).ne'
    have e1 : Formalism.QuantumDeterminants.Mdim S.G.k S.G.r l = MA.Mdim S.G.k S.G.r l := rfl
    rw [e1, pow_mul, Complex.sq_norm, show MA.Mdim S.G.k S.G.r l - 1 = (MA.Mdim S.G.k S.G.r l - 2) + 1 by omega,
      pow_succ]
    field_simp

  have hval : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v), ∀ ρ,
      ((trJ S T v e J ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) =
        fun q => ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
          inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq Db q.1))) := fun J hJ ρ =>
    toSm_val_of_mem (D.parOf S v) (trace_smoothness E Wp Wq S T v hplace e hFr J hJ ρ)

  have hR : ∀ ρ, MA.ip0 (trJ S T v e J₁ ρ) (trJ S T v e J₂ ρ) =
      ∫ x in Qs, ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x))))) := by
    intro ρ
    unfold MA.ip0
    rw [Formalism.FourierDecayAlt.P.MAx2.Adj.integral_base_measure]
    have hz : ∀ x, x ∉ Qs → ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
        MA.ext (r := (D.parOf S v).r) (TT := (D.parOf S v).TT)
          (fun q : MA.Qp (D.parOf S v).r (D.parOf S v).TT =>
            ((trJ S T v e J₁ ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q *
            conj (((trJ S T v e J₂ ρ : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
              MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) q)) x = 0 := by
      intro x hx
      rw [Formalism.FourierDecayAlt.P.MAx2.Adj.ext_out _ hx, mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    refine setIntegral_congr_fun hQm fun x hx => ?_
    simp only [MA.ext, hval J₁ hJ₁, hval J₂ hJ₂]
    rw [dite_eq_left (show x ∈ MA.Qset S.G.r (D.parOf S v).TT from hx)]
    rw [hW x hx, map_mul, Complex.conj_ofReal]
    have hw := wq_pos (k := S.G.k) hx
    have hs : ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) *
        ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ) = ((MA.wq S.G.k x (D.parOf S v).TT : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hw.le]
    push_cast
    linear_combination ((Formalism.FourierDecayAlt.P.MAx2.Adj.dR x : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))) * hs

  have hcont : ∀ J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v),
      ContinuousOn (fun x => B.hsVec (J (B.gq Db x))) Qs := fun J hJ =>
    hsVec_contDiff.continuous.comp_continuousOn (jgq_contDiffOn S T v hplace hJ).continuousOn
  have heC : ∀ ρ, ContinuousOn (fun x : MA.E S.G.r => B.hsVec (e ρ x.2)) Qs := fun ρ =>
    hsVec_contDiff.continuous.comp_continuousOn
      ((hFr.1 ρ).continuousOn.comp continuous_snd.continuousOn fun x hx => hx.2)
  have hU : ∀ (J) (hJ : J ∈ Q.FFl S.G.k S.G.r Db.z Db.z' Db.π Db.π' 0 (OmP S T v)),
      jNormSq S.G.k S.G.r (Tz S.G.k S.G.r Db.z) (Tz S.G.k S.G.r Db.z') (fun q => B.hsVec (J (B.gq Db q))) ≠ ⊤ →
      IntegrableOn (fun x => W x * ‖B.hsVec (J (B.gq Db x))‖ ^ 2) Qs := by
    intro J hJ hN
    refine ⟨((Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _).aestronglyMeasurable).mul
      (((hcont J hJ).norm.pow 2).aestronglyMeasurable hQm), ?_⟩
    refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => mul_nonneg (hW0 x) (sq_nonneg _))).2 ?_
    exact lt_of_le_of_lt (setLIntegral_le_lintegral Qs _) (lt_top_iff_ne_top.2 hN)
  have hInt : ∀ ρ, IntegrableOn (fun x => ((W x : ℝ) : ℂ) * (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x))) *
        conj (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))))) Qs := by
    intro ρ
    refine Integrable.mono' ((hU J₁ hJ₁ hN₁).add (hU J₂ hJ₂ hN₂)) ?_ ?_
    · exact ((Complex.measurable_ofReal.comp (Formalism.FourierDecayAlt.P.B7.measurable_bcWeight _ _)).aestronglyMeasurable).mul
        ((((heC ρ).inner (hcont J₁ hJ₁)).mul ((heC ρ).inner (hcont J₂ hJ₂)).star).aestronglyMeasurable hQm)
    · refine ae_restrict_of_forall_mem hQm fun x hx => ?_
      have he1 : ‖B.hsVec (e ρ x.2)‖ ≤ 1 := by
        have h1 : inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (e ρ x.2)) = (1 : ℂ) := by
          simpa using (hFr.2 x.2 hx.2).2.1 ρ ρ
        rw [inner_self_eq_norm_sq_to_K] at h1
        have h2' : ((‖B.hsVec (e ρ x.2)‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
          rw [Complex.ofReal_pow, Complex.ofReal_one]; exact h1
        have h2 : ‖B.hsVec (e ρ x.2)‖ ^ 2 = 1 := Complex.ofReal_injective h2'
        nlinarith [norm_nonneg (B.hsVec (e ρ x.2))]
      have ha : ∀ J : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J (B.gq Db x)))‖ ≤ ‖B.hsVec (J (B.gq Db x))‖ := fun J =>
        (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (B.hsVec (J (B.gq Db x)))])
      have hn1 := ha J₁
      have hn2 := ha J₂
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hW0 x), RCLike.norm_conj]
      have hp : ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))‖ *
          ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))‖ ≤
            ‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2 := by
        nlinarith [norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))),
          norm_nonneg (inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))),
          norm_nonneg (B.hsVec (J₁ (B.gq Db x))), norm_nonneg (B.hsVec (J₂ (B.gq Db x))),
          sq_nonneg (‖B.hsVec (J₁ (B.gq Db x))‖ - ‖B.hsVec (J₂ (B.gq Db x))‖)]
      calc W x * (‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₁ (B.gq Db x)))‖ *
            ‖inner ℂ (B.hsVec (e ρ x.2)) (B.hsVec (J₂ (B.gq Db x)))‖)
          ≤ W x * (‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hp (hW0 x)
        _ = W x * ‖B.hsVec (J₁ (B.gq Db x))‖ ^ 2 + W x * ‖B.hsVec (J₂ (B.gq Db x))‖ ^ 2 := by ring

  unfold MA.ipA
  simp_rw [hR]
  rw [← integral_finsetSum _ (fun ρ _ => hInt ρ)]
  unfold betaBig
  have hae : ∀ᵐ x ∂(volume : Measure ((Fin S.G.r → ℂ) × ℂ)), x ∉ Qs →
      ((W x : ℝ) : ℂ) * inner ℂ (B.hsVec (J₂ (bigCell S.G.k S.G.r x.1 (Db.μsec x.2))))
        (B.hsVec (J₁ (bigCell S.G.k S.G.r x.1 (Db.μsec x.2)))) = 0 := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem_good_set_or_weight_zero Db] with x hx hxQ
    rcases hx with hx | hx
    · exfalso
      apply hxQ
      refine ⟨hx.1, ?_⟩
      have h2 := hx.2
      rw [hTT] at h2
      exact h2
    · rw [show W x = 0 from hx]; simp
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hae]
  refine setIntegral_congr_fun hQm fun x hx => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hX := (hFr.2 x.2 hx.2).2.2 (J₁ (B.gq Db x)) (fibre_membership_holds E Wp Wq S T v hplace J₁ hJ₁ x hx)
  exact parseval (fun ρ => e ρ x.2) (J₁ (B.gq Db x)) (J₂ (B.gq Db x)) hX

end Formalism.FourierDecayAlt.P.CutMP.En
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPTop
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

section

variable {k r : ℕ}

theorem unipotent_fixes_anisotropic_vector (l : Fin r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) : Q.w1 k r l c *ᵥ v = v := by
  have hsum : v = ∑ q, v q • bvec q := by
    funext p
    simp [bvec, Finset.sum_apply, Pi.single_apply]
  rw [hsum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.mulVec_smul]
  by_cases h1 : q = eI k r l
  · have : v q = 0 := hv q (Or.inl (by rw [h1]; simp [eI]))
    rw [this, zero_smul, zero_smul]
  by_cases h2 : q = esI k r l
  · have : v q = 0 := hv q (Or.inr (by rw [h2]; simp [esI]; omega))
    rw [this, zero_smul, zero_smul]
  rw [Formalism.FourierDecayAlt.P.Qx3.reflection_fixes_basis_vector l c h1 h2]

theorem top_wlist_wb (c : Fin r → ℂ) (L : List (Fin r)) (v : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) :
    (L.map fun a => Q.w1 k r a (c a)).prod *ᵥ v = v := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.prod_cons, ← Matrix.mulVec_mulVec, ih, unipotent_fixes_anisotropic_vector a _ v hv]

theorem inv_wCell_last_mul_mulVec_of_inWb {c : Fin r → ℂ} (hc : c ∈ OmX r) {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r))
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (Q.wCell k r (Fin.last r) c * g)⁻¹ *ᵥ z = g⁻¹ *ᵥ z := by
  have hW : Q.wCell k r (Fin.last r) c ∈ Q.Glev k r 0 := Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _
  have hgu : IsUnit g.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg.1
  have hu : IsUnit (Q.wCell k r (Fin.last r) c * g).det := by
    rw [Matrix.det_mul]
    exact (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hW.1).mul hgu
  have hv : (Q.wCell k r (Fin.last r) c * g) *ᵥ (g⁻¹ *ᵥ z) = z := by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z g, Matrix.mul_nonsing_inv _ hgu, Matrix.one_mulVec]
    exact top_wlist_wb c _ z hz
  conv_lhs => rw [← hv]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem top_qminor_cast {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n t t' : ℕ}
    (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (h : t = t') (a b : Fin t' → Fin n) (u : ℂ) :
    qminorOp Eop (a ∘ Fin.cast h) (b ∘ Fin.cast h) u = qminorOp Eop a b u := by
  subst h
  rfl

theorem top_chatL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {t : ℕ} (h : t = k + 1)
    (pos : Fin t → Fin (2 * r + k + 1)) (hpos : ∀ j, (pos j).val = r + j.val) (u : ℂ)
    (a β : Q.Mx k r → Fin t → ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    Q.chatL (Q.EH k r) pos u a β f g = ∑ s : Fin (k + 1), ∑ t' : Fin (k + 1),
      (((-1 : ℂ) ^ ((s : ℕ) + (t' : ℕ))) * β g (Fin.cast h.symm s) * a g (Fin.cast h.symm t')) •
        qminorOp (Q.EH k r) (rowsN k r (Fin.last r) s) (rowsN k r (Fin.last r) t') u f g := by
  subst h
  unfold Q.chatL
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t' _ => ?_
  have hc : k + 1 - 1 = r - (Fin.last r).val + k := by simp
  have e : ∀ i : Fin (k + 1), pos ∘ Q.skip1 i = rowsN k r (Fin.last r) i ∘ Fin.cast hc := by
    intro i
    funext j
    apply Fin.ext
    simp only [Function.comp_apply, Q.skip1, rowsN, Fin.val_last, Fin.val_cast]
    split_ifs <;> simp_all <;> omega
  rw [e s, e t', top_qminor_cast]
  rfl

end

theorem residue_top_holds : JDRTop := by
  intro Wp Wq _ _ _ _ k r z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  have hm : Q.mdim k r (Fin.last r) = k + 1 := by simp [Q.mdim]
  have hpos : ∀ j, (Q.posL k r (Fin.last r) j).val = r + j.val := fun j => by
    simp [Q.posL]; omega
  simp only [FN, Q.resG, Q.QL, Q.grp, Q.tL, Pi.neg_apply, neg_neg]
  have e1 : Q.resG k r (Fin.last r) J c =
      ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖c a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ) •
        (fun g' => J (Q.wCell k r (Fin.last r) c * g')) := rfl
  rw [e1, Formalism.FourierDecayAlt.P5.chatL_smulC, Pi.smul_apply]
  congr 1
  rw [top_chatL hm _ hpos]
  unfold NL
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian, inv_wCell_last_mul_mulVec_of_inWb hc hg hz]
  congr 2
  · congr 1
    simp only [Q.xbv, fvec]
    congr 1
    · congr 1; apply Fin.ext; simp [Q.posL, wI]; omega
    · simp
  · simp only [Q.yv, fvec]
    congr 2
    · simp
    · apply Fin.ext; simp [Q.posL, wI]; omega

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPPComm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

def JDRPComm : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (Dc : (Fin r → ℂ) → Set (Q.Mx k r)) (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)), inWb k r z → inWb k r z' →
    IsOpen {x : (Fin r → ℂ) × Q.Mx k r | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1} →
    Q.FamFF k r z z' π π' (Fin.last r) Dc Ψ →
    ∀ (l : Fin r) (Y : ℂ) (a b : Fin 2), ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), g ∈ Dc c →
      Q.crd (Formalism.QuantumDeterminants.pOp l) (Q.QL k r z z' (Fin.last r) Y a b Ψ) c g =
        Q.QL k r z z' (Fin.last r) Y a b (Q.crd (Formalism.QuantumDeterminants.pOp l) Ψ) c g

end

end Formalism.FourierDecayAlt.P.CutMP
end
