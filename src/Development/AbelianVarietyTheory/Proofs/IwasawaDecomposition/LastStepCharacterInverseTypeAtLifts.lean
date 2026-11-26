module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimeRowTypeTopRestrictionMulLevelCharEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimeRowTypeTopRestrictionMulLevelCharEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TopRowsQ

open GlobalTheory.TopStep GlobalTheory.Mem.Col2 GlobalTheory.TopLaw

theorem redV_eq_of_cong {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {c : ℕ}
    (hc : 0 < c) {a b : Sp E n} (hb : b ∈ stdAt E n P) (h : (((qOf P : ℕ) : E) ^ c)⁻¹ • (a - b) ∈ stdAt E n P) :
    a ∈ stdAt E n P ∧ redV P a = redV P b := by
  have hq := qOf_ne_zero (P := P)
  have h1 : ∀ i, IntAt P ((((qOf P : ℕ) : E) ^ c)⁻¹ * (a i - b i)) := fun i => mem_stdAt.1 h i
  have h2 : ∀ i, IntAt P (a i - b i) := fun i => by
    have h3 := (intAt_pow (intAt_nat (P := P) (qOf P)) c).mul (h1 i)
    convert h3 using 1
    field_simp
  have ha : ∀ i, IntAt P (a i) := fun i => by
    have h3 := (h2 i).add (mem_stdAt.1 hb i)
    convert h3 using 1
    ring
  refine ⟨mem_stdAt.2 ha, funext fun i => ?_⟩
  have h4 : redP P (a i - b i) = 0 := by
    apply redP_eq_zero_of_div
    have h3 := (intAt_pow (intAt_nat (P := P) (qOf P)) (c - 1)).mul (h1 i)
    convert h3 using 1
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [reduction_sub (ha i) (mem_stdAt.1 hb i), sub_eq_zero] at h4
  exact h4

theorem lamQB_mul_levCong : ∀ {X : Fields} {R : Ranks} (ξ : Chr X.F X.E X.K) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) (c M : ℕ), 1 ≤ M →
    ∀ (k : Formalism.L2.Col.GLint X.E (R.N R.m) P.1) (hk : k ∈ (levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).H)
    (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JQ P.1 (qOf P.1) R.r (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    CongE P.1 (2 * M) g (k⁻¹).1 →
    LocE.lamQB (resChar ξ P.1) R.r (R.N R.m - 1) g''.toLinearMap *
      (((levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).lam ⟨k, hk⟩ : X.Kˣ) : X.K) = 1 := by
  intro X R ξ Q P c M hM k hk g g'' hJ hpr hC
  have hN := N_m_succ R
  obtain ⟨j, hj, hb⟩ := (mem_levCong (N_m_succ R) c _ k).1 hk
  rw [levCong_lam (N_m_succ R) c _ hk hj hb, levRed_lam]
  have ek : redGL _ P.1 k = diagEmb _ (by omega : R.N R.m - 1 ≤ R.N R.m) (redGL _ P.1 j) := by
    have e := redGL_of_prinCong c.succ_pos hb
    rw [map_mul, map_inv, inv_mul_eq_one, redGL_extI] at e
    exact e.symm
  let g2 : Formalism.L2.Col.GLint X.E (R.N R.m - 1) P.1 := ⟨g'', hJ.1⟩
  have hred : redGL _ P.1 g2 = (redGL _ P.1 j)⁻¹ := by
    refine redGL_eq g2 fun x hx => ?_
    let v : Sp X.E (R.N R.m) := fun l => if h : l.1 < R.N R.m - 1 then x ⟨l.1, h⟩ else 0
    have hv : v ∈ stdAt X.E (R.N R.m) P.1 := mem_stdAt.2 fun l => by
      by_cases h : l.1 < R.N R.m - 1
      · simp only [v, dif_pos h]; exact mem_stdAt.1 hx _
      · simp only [v, dif_neg h]; simpa using intAt_nat (P := P.1) 0
    have hpv : prXpG X.E (R.N R.m) v = x := by
      funext i
      show v _ = x i
      simp only [v, dif_pos (show i.1 < R.N R.m - 1 from i.2)]
      rfl
    have hxg : g'' x = prXpG X.E (R.N R.m) (g v) := by
      have := LinearMap.congr_fun hpr v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hpv] at this
      exact this.symm
    obtain ⟨-, e1⟩ := redV_eq_of_cong (by omega : 0 < 2 * M) (glint_mem k⁻¹ hv) (hC v hv)
    have e2 := redV_redGL k⁻¹ hv
    rw [map_inv, ek, ← map_inv, diagEmb_val] at e2
    funext i
    have e3 := congrFun e1 (Br.iC hN i)
    rw [e2, (diagMat_mulVec hN _ _).1] at e3
    show redP P.1 (g'' x i) = _
    rw [hxg]
    refine e3.trans ?_
    congr 1
    funext l
    show redP P.1 (v (Br.iC hN l)) = redP P.1 (x l)
    simp only [v, Br.iC, dif_pos l.2]
  have hH : redGL _ P.1 g2 ∈ HQ (𝓞 X.E ⧸ P.1.asIdeal) (R.N R.m - 1) R.r (R.m * R.t) := hred ▸ inv_mem hj
  have hl := lamQB_eq_red (resChar ξ P.1) (rank_X'_eq R) g2 hH
  rw [show (g''.toLinearMap : HomE X.E _ _) = g2.1.toLinearMap from rfl, hl]
  have e4 : lamQ (resChar ξ P.1) _ R.r (R.m * R.t) ⟨redGL _ P.1 g2, hH⟩ =
      (lamQ (resChar ξ P.1) _ R.r (R.m * R.t) ⟨redGL _ P.1 j, hj⟩)⁻¹ := by
    rw [← map_inv]
    exact congrArg _ (Subtype.ext hred)
  rw [← Units.val_mul, e4]
  show (((_ : X.Kˣ)⁻¹)⁻¹ * (lamQP ξ P.1 (R.N R.m - 1) R.r (R.m * R.t) ⟨redGL _ P.1 j, hj⟩)⁻¹ : X.Kˣ).1 = 1
  rw [inv_inv, lamQP, mul_inv_cancel, Units.val_one]

end GlobalTheory.TopRowsQ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistPrimeRowTypeTopRestrictionMulLevelCharEqOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrime_rowType_topRestriction_mul_levelChar_eq_one : ∀ {X : Fields} {R : Ranks} (ξ : Chr X.F X.E X.K) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) (c M : ℕ), 1 ≤ M →
    ∀ (k : Formalism.L2.Col.GLint X.E (R.N R.m) P.1) (hk : k ∈ (levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).H)
    (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JQ P.1 (qOf P.1) R.r (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    CongE P.1 (2 * M) g (k⁻¹).1 →
    LocE.lamQB (resChar ξ P.1) R.r (R.N R.m - 1) g''.toLinearMap *
      (((levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).lam ⟨k, hk⟩ : X.Kˣ) : X.K) = 1 := by
  first | exact @GlobalTheory.TopRowsQ.lamQB_mul_levCong | exact GlobalTheory.TopRowsQ.lamQB_mul_levCong | (intros; apply GlobalTheory.TopRowsQ.lamQB_mul_levCong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeRowTypeTopRestrictionMulLevelCharEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeRowTypeTopRestrictionMulLevelCharEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

open GlobalTheory.TopStep GlobalTheory.LastSteps

theorem lamGBS_top_mul_lam_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs})
    (h0 : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hh0 : h0 ∈ (rowTyG Ch (rPsymF Ch) w).H)
    (g g' : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    g' ∈ Formalism.L2.Col.GLint X.E (R.N R.m) w.1 →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (g' x) =
      ((diagEmb (𝓞 X.E ⧸ w.1.asIdeal) (Nat.sub_le (R.N R.m) 1) h0)⁻¹ : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal)).1.mulVec (redV w.1 x)) →
    CongE w.1 1 g g' →
    LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap *
      (((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) : X.K) = 1 := by
  intro X Pr R Ch w h0 hh0 g g' g'' hJ hcomm hg' hred hcong
  classical
  obtain ⟨σ₀⟩ : Nonempty (X.K →+* ℂ) := inferInstance
  have hN : R.N R.m = (R.N R.m - 1) + 1 := N_m_succ R
  have ht := t_pos R
  have hrr := r_eq_sym R
  have hX' := rank_X'_eq R
  have hint : g'' ∈ GLint X.E (R.N R.m - 1) w.1 := by
    intro x
    have h1 := (Subgroup.mem_inf.1 hJ).1 x
    rwa [lamY_zero] at h1
  have hredr : ∀ x ∈ stdAt X.E (R.N R.m - 1) w.1, redV w.1 (g'' x) = (h0⁻¹).1.mulVec (redV w.1 x) := by
    intro x hx
    let v : Sp X.E (R.N R.m) := fun l => if hl : l.1 < R.N R.m - 1 then x ⟨l.1, hl⟩ else 0
    have hv : v ∈ stdAt X.E (R.N R.m) w.1 := by
      rw [mem_stdAt]
      intro l
      by_cases hl : l.1 < R.N R.m - 1
      · simp only [v, dif_pos hl]
        exact mem_stdAt.1 hx _
      · simp only [v, dif_neg hl]
        exact intAt_zero
    have hpv : prXpG X.E (R.N R.m) v = x := by
      funext i
      have hi : i.1 < R.N R.m - 1 := i.2
      simp [prXpG, LinearMap.funLeft_apply, v, hi]
    have hgx : g'' x = prXpG X.E (R.N R.m) (g v) := by
      have h2 := LinearMap.congr_fun hcomm v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h2
      rw [h2, hpv]
    have hc := hcong v hv
    funext i
    have eL : redV w.1 (g'' x) i = redV w.1 (g' v) (Br.iC hN i) := by
      rw [hgx]
      show redP w.1 (g v (Br.iC hN i)) = redP w.1 (g' v (Br.iC hN i))
      have hz := mem_stdAt.1 hc (Br.iC hN i)
      have hq : ((qOf w.1 : ℕ) : X.E) ≠ 0 := qOf_ne_zero
      have e : g v (Br.iC hN i) = g' v (Br.iC hN i) +
          (qOf w.1 : X.E) * (((((qOf w.1 : ℕ) : X.E) ^ 1)⁻¹ • (g v - g' v)) (Br.iC hN i)) := by
        simp only [pow_one, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [mul_inv_cancel_left₀ hq]
        ring
      rw [e, redP_add_q hz]
    rw [eL, hred v hv, ← map_inv, diagEmb_val, (diagMat_mulVec hN _ _).1 i]
    congr 1
    funext j
    show redP w.1 (v (Br.iC hN j)) = redP w.1 (x j)
    have hj : (Br.iC hN j).1 < R.N R.m - 1 := j.2
    simp only [v, dif_pos hj]
    rfl
  have hM : h0⁻¹ ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := inv_mem hh0
  have e1 : psi0P Ch w.1 = Ch.psi0 w := by
    unfold psi0P
    rw [dif_pos w.2]
  have e2 : chiP Ch w.1 = chiAt Ch w := by
    unfold chiP
    rw [dif_pos w.2]
  have hlam : LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap =
      ((lamJsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h0⁻¹, hM⟩ : X.Kˣ) : X.K) := by
    rw [e1, e2]
    exact clW_lamGBS_lamJsym σ₀ _ _ hrr ht (by omega) (r_le_X' R) (by omega) ⟨h0⁻¹, hM⟩ g'' hint hredr
  have hr : ((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) =
      lamJsym (Ch.psi0 w) (chiAt Ch w) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h0, hh0⟩ := rfl
  have hprod : (⟨h0⁻¹, hM⟩ * ⟨h0, hh0⟩ : ↥(HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R))) = 1 :=
    Subtype.ext (inv_mul_cancel h0)
  rw [hlam, hr, ← Units.val_mul, ← map_mul, hprod, map_one, Units.val_one]

end GlobalTheory.Mem.Col2.AdT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeRowTypeTopRestrictionMulLevelCharEqOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrime_rowType_topRestriction_mul_levelChar_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (w : {w // w ∈ Pr.vGs})
    (h0 : GL (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) (hh0 : h0 ∈ (rowTyG Ch (rPsymF Ch) w).H)
    (g g' : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    g' ∈ Formalism.L2.Col.GLint X.E (R.N R.m) w.1 →
    (∀ x ∈ stdAt X.E (R.N R.m) w.1, redV w.1 (g' x) =
      ((diagEmb (𝓞 X.E ⧸ w.1.asIdeal) (Nat.sub_le (R.N R.m) 1) h0)⁻¹ : GL (Fin (R.N R.m)) (𝓞 X.E ⧸ w.1.asIdeal)).1.mulVec (redV w.1 x)) →
    CongE w.1 1 g g' →
    LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 g''.toLinearMap *
      (((rowTyG Ch (rPsymF Ch) w).lam ⟨h0, hh0⟩ : X.Kˣ) : X.K) = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one | exact GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one | (intros; apply GlobalTheory.Mem.Col2.AdT.lamGBS_top_mul_lam_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepCharacterInverseTypeAtLifts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

theorem chr_mul_prod_top_core {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι)
    (Λ : LevFam B.fields.E B.fields.K (B.R.N B.R.m) (B.primes X).vGs)
    (hΛ : ∀ w, Λ w = levDiag (Nat.sub_le _ 1) (rowTyG I.Ch (rPsymF I.Ch) w))
    (Θ : LevQFam B.fields.E B.fields.K (B.R.N B.R.m) (I.Q a))
    (hΘ : ∀ Q, Θ Q = levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
      (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q))
    (x : Λ.grp) (y : Θ.grp)
    (g g' : SBof I a → Sp B.fields.E (B.R.N B.R.m) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N B.R.m)) (z : SBof I a → B.fields.K)
    (H : ∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) B.R.m P (g P) (z P) ∧
      (g' P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N B.R.m) P.1 ∧
        (∀ h : P.1 ∈ (B.primes X).vGs, ∀ v ∈ stdAt B.fields.E (B.R.N B.R.m) P.1,
          redV P.1 (g' P v) = ((x.1 ⟨P.1, h⟩)⁻¹).1.mulVec (redV P.1 v)) ∧
        ∀ h : P.1 ∈ I.Q a, g' P = ((y.1 ⟨P.1, h⟩)⁻¹).1) ∧
      CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) :
    (((Λ.chr x * Θ.chr y : B.fields.Kˣ) : B.fields.K)) * ∏ P, z P = 1 := by
  classical
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_left.2 fun P h1 h2 => Q_notMem_of_ok hOk a P h2 h1
  have e2 : ∏ P, z P = (∏ w : (B.primes X).vGs, z ⟨w.1, Finset.mem_union_left _ w.2⟩) *
      ∏ Q : I.Q a, z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ := by
    rw [← Fintype.prod_equiv (Equiv.Finset.union _ _ hd) _ _ (fun _ => rfl), Fintype.prod_sum_type]
    rfl
  rw [e2, LevFam.chr_apply, levQ_chr_apply, Units.val_mul, Units.coe_prod, Units.coe_prod]
  have hG : ∀ w : (B.primes X).vGs, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨w.1, Finset.mem_union_left _ w.2⟩ = 1 := by
    intro w
    obtain ⟨⟨g'', hg''m, hpr, -, hz⟩, ⟨hg'G, hred, -⟩, hc⟩ := H ⟨w.1, Finset.mem_union_left _ w.2⟩
    have key : ∀ (l : Lev (𝓞 B.fields.E ⧸ w.1.asIdeal) B.fields.K (B.R.N B.R.m)),
        l = levDiag (Nat.sub_le _ 1) (rowTyG I.Ch (rPsymF I.Ch) w) → ∀ A (hA : A ∈ l.H),
        ∃ h0, ∃ hh0 : h0 ∈ (rowTyG I.Ch (rPsymF I.Ch) w).H, A = diagEmb _ (Nat.sub_le (B.R.N B.R.m) 1) h0 ∧
          l.lam ⟨A, hA⟩ = (rowTyG I.Ch (rPsymF I.Ch) w).lam ⟨h0, hh0⟩ := by
      intro l hl A hA
      subst hl
      obtain ⟨h0, hh0, rfl⟩ := hA
      exact ⟨h0, hh0, rfl, levDiag_lam _ _ rfl _ hh0⟩
    obtain ⟨h0, hh0, eA, elam⟩ := key _ (hΛ w) _ (x.2 w (Set.mem_univ w))
    rw [elam]
    have hmem : g'' ∈ LocE.JGsym w.1 (qOf w.1) B.R.k B.R.rS B.R.r B.R.t (B.R.N B.R.m - 1) 0 := by
      have h1 := hg''m
      unfold GlobalTheory.TwU.rowLevTop at h1
      rwa [if_pos w.2, hOk.sharp a, if_pos rfl] at h1
    have hz' : z ⟨w.1, Finset.mem_union_left _ w.2⟩ = LocE.lamGBS (qOf w.1) (psi0P I.Ch w.1) (chiP I.Ch w.1)
        B.R.k B.R.r B.R.t B.R.m (B.R.N B.R.m - 1) 0 g''.toLinearMap := by
      rw [hz]
      unfold GlobalTheory.TwU.rowChrTop
      rw [if_pos w.2, hOk.sharp a, if_pos rfl]
    have eA' : x.1 ⟨w.1, w.2⟩ = diagEmb _ (Nat.sub_le (B.R.N B.R.m) 1) h0 := eA
    have hred' : ∀ v ∈ stdAt B.fields.E (B.R.N B.R.m) w.1, redV w.1 (g' ⟨w.1, Finset.mem_union_left _ w.2⟩ v) =
        ((diagEmb (𝓞 B.fields.E ⧸ w.1.asIdeal) (Nat.sub_le (B.R.N B.R.m) 1) h0)⁻¹ : GL (Fin (B.R.N B.R.m)) _).1.mulVec (redV w.1 v) := by
      intro v hv
      rw [hred w.2 v hv, eA']
    have hc' : CongE w.1 1 (g ⟨w.1, Finset.mem_union_left _ w.2⟩) (g' ⟨w.1, Finset.mem_union_left _ w.2⟩) := by
      have h1 := hc
      unfold GlobalTheory.TwU.topDep at h1
      rwa [if_pos w.2] at h1
    rw [mul_comm, hz']
    exact GlobalTheory.T.typePrime_rowType_topRestriction_mul_levelChar_eq_one I.Ch w h0 hh0 _ _ g'' hmem hpr hg'G hred' hc'
  have hQ : ∀ Q : I.Q a, (((Θ Q).lam ⟨y.1 Q, y.2 Q (Set.mem_univ Q)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ = 1 := by
    intro Q
    obtain ⟨⟨g'', hg''m, hpr, -, hz⟩, ⟨-, -, hgy⟩, hc⟩ := H ⟨Q.1, Finset.mem_union_right _ Q.2⟩
    have hnot : Q.1 ∉ (B.primes X).vGs := Q_notMem_of_ok hOk a Q.1 Q.2
    have key : ∀ (l : LevI B.fields.E B.fields.K (B.R.N B.R.m) Q.1),
        l = levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M) (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q) →
        ∀ k (hk : k ∈ l.H), ∃ hk' : k ∈ (levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
          (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q)).H,
          l.lam ⟨k, hk⟩ = (levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
            (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q)).lam ⟨k, hk'⟩ := by
      intro l hl k hk
      subst hl
      exact ⟨hk, rfl⟩
    obtain ⟨hk', elam⟩ := key _ (hΘ Q) _ (y.2 Q (Set.mem_univ Q))
    rw [elam]
    have hmem : g'' ∈ LocE.JQ Q.1 (qOf Q.1) B.R.r (B.R.N B.R.m - 1) 0 := by
      have h1 := hg''m
      unfold GlobalTheory.TwU.rowLevTop at h1
      rwa [if_neg hnot] at h1
    have hz' : z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ = LocE.lamQB (resChar (I.tup a : Chr B.fields.F B.fields.E B.fields.K) Q.1)
        B.R.r (B.R.N B.R.m - 1) g''.toLinearMap := by
      rw [hz]
      unfold GlobalTheory.TwU.rowChrTop
      rw [if_neg hnot]
    have hc' : CongE Q.1 (2 * (I.cst a).M) (g ⟨Q.1, Finset.mem_union_right _ Q.2⟩) ((y.1 Q)⁻¹).1 := by
      have h1 := hc
      unfold GlobalTheory.TwU.topDep at h1
      rw [if_neg hnot, hgy Q.2] at h1
      exact h1
    rw [mul_comm, hz']
    exact GlobalTheory.T.twistPrime_rowType_topRestriction_mul_levelChar_eq_one (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q _ _ (hOk.idx_ok a).cst_ok.M_pos (y.1 Q) hk' _ g'' hmem hpr hc'
  calc _ = (∏ w : (B.primes X).vGs, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : B.fields.Kˣ) : B.fields.K) *
        z ⟨w.1, Finset.mem_union_left _ w.2⟩) * ∏ Q : I.Q a, (((Θ Q).lam ⟨y.1 Q, y.2 Q (Set.mem_univ Q)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
    _ = 1 := by
        rw [Finset.prod_eq_one fun w _ => hG w, Finset.prod_eq_one fun Q _ => hQ Q, one_mul]

theorem chr_mul_prod_topVal : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  intro B X I hOk u a i hi b κ g g' z H
  subst hi
  rcases b with ⟨_ | b1, hb⟩
  swap
  · exact absurd (hb.1 rfl) (lt_irrefl _)
  exact chr_mul_prod_top_core I hOk a _ (fun w => congrFun (topLevAt_levG_m I.Ch I.sel (I.tup a) I.Ps _) w) _
    (fun Q => congrFun (topLevAt_levQ_m I.Ch I.sel (I.tup a) I.Ps _) Q) κ.2.1 κ.2.2 g g' z H

end GlobalTheory.Mem.Col2.AdT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepCharacterInverseTypeAtLiftsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_step_character_inverse_type_at_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  first | exact @GlobalTheory.Mem.Col2.AdT.chr_mul_prod_topVal | exact GlobalTheory.Mem.Col2.AdT.chr_mul_prod_topVal | (intros; apply GlobalTheory.Mem.Col2.AdT.chr_mul_prod_topVal <;> assumption)
end
