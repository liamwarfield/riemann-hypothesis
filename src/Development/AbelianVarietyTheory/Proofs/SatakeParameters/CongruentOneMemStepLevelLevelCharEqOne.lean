module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockDetResidueCharEqOneOfCongModQ
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockDetResidueCharEqOneOfCongModQ
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamQBCong

open GlobalTheory.TopStep

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

theorem entry_cong (P : HeightOneSpectrum (𝓞 E)) {N : ℕ} (g : HomE E N N)
    (hg : ∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) (s t : Fin N) :
    IntAt P (g (Pi.single t 1) s) ∧ redP P (g (Pi.single t 1) s) = if s = t then 1 else 0 := by
  classical
  have hq0 : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hx := mem_stdAt.1 (hg _ (single_mem_stdAt (P := P) t)) s
  set δ : E := (Pi.single t (1 : E) : Sp E N) s with hδ
  have hδI : IntAt P δ := mem_stdAt.1 (single_mem_stdAt (P := P) t) s
  have hdiv : IntAt P ((g (Pi.single t 1) s - δ) / (qOf P : E)) := by
    have e : (((qOf P : E)⁻¹ • (g (Pi.single t 1) - Pi.single t 1) : Sp E N)) s = (g (Pi.single t 1) s - δ) / (qOf P : E) := by
      rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [← e]
    exact hx
  have hI : IntAt P (g (Pi.single t 1) s - δ) := by
    have e : g (Pi.single t 1) s - δ = (qOf P : E) * ((g (Pi.single t 1) s - δ) / (qOf P : E)) := by
      field_simp
    rw [e]
    exact (intAt_nat _).mul hdiv
  have hI' : IntAt P (g (Pi.single t 1) s) := by
    have := intAt_sub hI (intAt_neg hδI)
    rwa [sub_neg_eq_add, sub_add_cancel] at this
  refine ⟨hI', ?_⟩
  have h0 := redP_eq_zero_of_div hdiv
  rw [reduction_sub hI' hδI, sub_eq_zero] at h0
  rw [h0, hδ, Pi.single_apply]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

theorem lamQB_eq_one_of_cong : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))
    (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n N : ℕ) (g : HomE E N N), n ≤ N →
    (∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) → LocE.lamQB ξ kj n g = 1 := by
  intro E K _ _ _ _ P ξ kj n N g hn hg
  classical
  unfold LocE.lamQB
  set D : Matrix (Fin (n - kj)) (Fin (n - kj)) E := Matrix.of fun s t : Fin (n - kj) =>
    Loc.atN (g (Loc.eN E N (kj + t.1))) (kj + s.1) with hD
  have hent : ∀ s t : Fin (n - kj), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 E ⧸ P.asIdeal)) s t := by
    intro s t
    have hs : kj + s.1 < N := by have := s.2; omega
    have ht : kj + t.1 < N := by have := t.2; omega
    have e1 : Loc.eN E N (kj + t.1) = Pi.single ⟨kj + t.1, ht⟩ 1 := by
      funext l
      unfold Loc.eN
      rw [Pi.single_apply]
      congr 1
      apply propext
      constructor
      · intro h; exact Fin.ext h
      · intro h; rw [h]
    have e2 : D s t = g (Pi.single ⟨kj + t.1, ht⟩ 1) ⟨kj + s.1, hs⟩ := by
      rw [hD, Matrix.of_apply, e1]
      unfold Loc.atN
      rw [dite_eq_left hs]
    obtain ⟨h1, h2⟩ := entry_cong P g hg ⟨kj + s.1, hs⟩ ⟨kj + t.1, ht⟩
    rw [e2]
    refine ⟨h1, ?_⟩
    rw [h2, Matrix.one_apply]
    by_cases hst : s = t
    · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst]
    · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst]
  have hdet : redP P D.det = 1 := by
    rw [(det_int fun s t => (hent s t).1).2]
    have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
    rw [this, Matrix.det_one]
  unfold LocE.unitV
  have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
  rw [dite_eq_left hu]
  have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
  rw [this, map_one, Units.val_one, inv_one]

end GlobalTheory.LamQBCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockDetResidueCharEqOneOfCongModQStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockDetResidueChar_eq_one_of_cong_mod_q : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n N : ℕ) (g : HomE E N N), n ≤ N → (∀ x ∈ stdAt E N P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E N P) → LocE.lamQB ξ kj n g = 1 := by
  first | exact @GlobalTheory.LamQBCong.lamQB_eq_one_of_cong | exact GlobalTheory.LamQBCong.lamQB_eq_one_of_cong | (intros; apply GlobalTheory.LamQBCong.lamQB_eq_one_of_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfCongOneModQ
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfCongOneModQ
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.ParahoricOfCong

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))

theorem mem_stdAt_iff_sclLat_zero (q N : ℕ) (x : Sp E N) :
    x ∈ stdAt E N P ↔ x ∈ LocE.sclLat P q N (fun _ => 0) := by
  rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
  simp

theorem map_mem_of_cong {N : ℕ} (q : E) (M : Submodule (𝓞 E) (Sp E N)) (hM : M ≤ stdAt E N P)
    (hqM : ∀ y : Sp E N, q⁻¹ • y ∈ stdAt E N P → y ∈ M)
    (h : Sp E N ≃ₗ[E] Sp E N) (hh : ∀ x ∈ stdAt E N P, q⁻¹ • (h x - x) ∈ stdAt E N P) :
    ∀ x ∈ M, h x ∈ M := by
  intro x hx
  have e : h x = x + (h x - x) := by abel
  rw [e]
  exact M.add_mem hx (hqM _ (hh x (hM hx)))

theorem mem_stabL_of_cong {N : ℕ} (q : E) (M : Submodule (𝓞 E) (Sp E N)) (hM : M ≤ stdAt E N P)
    (hqM : ∀ y : Sp E N, q⁻¹ • y ∈ stdAt E N P → y ∈ M)
    (g : Sp E N ≃ₗ[E] Sp E N) (h1 : ∀ x ∈ stdAt E N P, q⁻¹ • (g x - x) ∈ stdAt E N P)
    (h2 : ∀ x ∈ stdAt E N P, q⁻¹ • (g⁻¹ x - x) ∈ stdAt E N P) :
    g ∈ stabL E N M := by
  intro x
  constructor
  · intro hx
    have := map_mem_of_cong P q M hM hqM g⁻¹ h2 (g x) hx
    have e : g⁻¹ (g x) = x := LinearEquiv.symm_apply_apply g x
    rwa [e] at this
  · exact map_mem_of_cong P q M hM hqM g h1 x

end GlobalTheory.ParahoricOfCong


open GlobalTheory.ParahoricOfCong in
theorem GlobalTheory.ParahoricOfCong.mem_JQ_of_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (kj n c : ℕ) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)), (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E (n + c) P) → (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g⁻¹ x - x) ∈ stdAt E (n + c) P) → g ∈ LocE.JQ P (qOf P) kj n c := by
  intro E _ _ _ P kj n c g h1 h2
  have hq : ((qOf P : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero (P := P)
  refine ⟨?_, ?_⟩
  · refine mem_stabL_of_cong P _ _ le_rfl (fun y hy => ?_) g h1 h2
    have e : y = (qOf P : E) • ((qOf P : E)⁻¹ • y) := by rw [smul_smul, mul_inv_cancel₀ hq, one_smul]
    rw [e, Nat.cast_smul_eq_nsmul E]
    exact nsmul_mem hy _
  · refine mem_stabL_of_cong P _ _ ?_ ?_ g h1 h2
    · intro x hx
      rw [mem_stdAt_iff_sclLat_zero P (qOf P)]
      have := GlobalTheory.CongLevel.sclLat_le P (qOf P) hq (n + c) (fun _ => 0) (fun l => kj ≤ l ∧ l < n)
      exact this (by simpa [LocE.parL] using hx)
    · intro y hy
      rw [mem_stdAt_iff_sclLat_zero P (qOf P)] at hy
      have := GlobalTheory.CongLevel.smul_mem_sclLat P (qOf P) hq (n + c) (fun _ => 0) (fun l => kj ≤ l ∧ l < n) y hy
      simpa [LocE.parL] using this
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfCongOneModQStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_parahoric_of_cong_one_mod_q : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (kj n c : ℕ) (g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)), (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g x - x) ∈ stdAt E (n + c) P) → (∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • (g⁻¹ x - x) ∈ stdAt E (n + c) P) → g ∈ LocE.JQ P (qOf P) kj n c := by
  first | exact @GlobalTheory.ParahoricOfCong.mem_JQ_of_cong | exact GlobalTheory.ParahoricOfCong.mem_JQ_of_cong | (intros; apply GlobalTheory.ParahoricOfCong.mem_JQ_of_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjExtendPrincipalCongruenceCongOneModQ
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjExtendPrincipalCongruenceCongOneModQ
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.QCong

theorem conj_extE_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (c j D : ℕ) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : GLint E n P), κ ∈ GlobalTheory.TopStep.prinCong n P D → j + 1 ≤ D → (∀ x ∈ stdAt E (n + c) P, h⁻¹ x ∈ stdAt E (n + c) P ∧ ((qOf P : E) ^ j) • h x ∈ stdAt E (n + c) P) → ∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • ((h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x) ∈ stdAt E (n + c) P := by
  intro E _ _ _ P n c j D h κ hκ hjD hh x hx
  obtain ⟨m, rfl⟩ : ∃ m, D = j + 1 + m := ⟨D - (j + 1), by omega⟩
  have hq : ((qOf P : ℕ) : E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hu := (hh x hx).2
  have hw : GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x) ∈ stdAt E n P :=
    GlobalTheory.TopStep.mem_stdAt.2 fun i => GlobalTheory.TopStep.mem_stdAt.1 hu (Fin.castAdd c i)
  have hw' := (GlobalTheory.TopStep.mem_prinCong.1 hκ) _ hw
  have key : (qOf P : E)⁻¹ • (GlobalTheory.CongLevel.extE c κ.1 (h x) - h x) = ((qOf P : E) ^ m) • Loc.inX E n c
      ((((qOf P : E) ^ (j + 1 + m))⁻¹) • (κ.1 (GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x)) - GlobalTheory.CongLevel.resX c (((qOf P : E) ^ j) • h x))) := by
    rw [GlobalTheory.CongLevel.extE_apply, add_sub_cancel_left, map_smul (GlobalTheory.CongLevel.resX c), map_smul κ.1, ← smul_sub, smul_smul,
      ← map_smul, ← map_smul, smul_smul]
    congr 2
    field_simp
    ring
  have e1 : (h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x = h⁻¹ (GlobalTheory.CongLevel.extE c κ.1 (h x) - h x) := by
    rw [map_sub]
    congr 1
    exact (LinearEquiv.symm_apply_apply h x).symm
  rw [e1, ← map_smul, key]
  refine (hh _ ?_).1
  refine GlobalTheory.TopStep.mem_stdAt.2 fun l => ?_
  rw [Pi.smul_apply, smul_eq_mul, GlobalTheory.CongLevel.inX_apply]
  split_ifs with hl
  · exact (GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) m).mul (GlobalTheory.TopStep.mem_stdAt.1 hw' _)
  · rw [mul_zero]; exact GlobalTheory.TopStep.intAt_zero

end GlobalTheory.QCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjExtendPrincipalCongruenceCongOneModQStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (c j D : ℕ) (h : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : GLint E n P), κ ∈ GlobalTheory.TopStep.prinCong n P D → j + 1 ≤ D → (∀ x ∈ stdAt E (n + c) P, h⁻¹ x ∈ stdAt E (n + c) P ∧ ((qOf P : E) ^ j) • h x ∈ stdAt E (n + c) P) → ∀ x ∈ stdAt E (n + c) P, (qOf P : E)⁻¹ • ((h⁻¹ * GlobalTheory.CongLevel.extE c κ.1 * h) x - x) ∈ stdAt E (n + c) P := by
  first | exact @GlobalTheory.QCong.conj_extE_cong | exact GlobalTheory.QCong.conj_extE_cong | (intros; apply GlobalTheory.QCong.conj_extE_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelLevelCharEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LevOne

theorem cong_mem_level_chr_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hCh hsel hL j hj b P k hk
  classical
  obtain ⟨hkG, hkC⟩ := GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong P.1 (cst.D P) k (hL.cst_ok.D_pos P) hk
  set κ : GLint X.E (R.N j) P.1 := ⟨k, hkG⟩ with hκdef
  have hψ : cst.psi P (Loc.n1Arg (GlobalTheory.CongLevel.extE (cOf R j) k)) = 1 := by
    rw [GlobalTheory.Mem.Col2.LevMod.unipotentArg_extendByIdOnLastCoords]
    exact hL.cst_ok.psi_int P 0 (by simpa using GlobalTheory.CongLevel.intAt_nat P.1 0)
  have hq : ((qOf P.1 : ℕ) : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  by_cases hP : P.1 ∈ Pr.vGs
  · have hD1 : cst.D P = 1 := hL.depthG P hP
    have hdu := GlobalTheory.Mem.Col2.degOneUnram_of_mem_vGs hX.ok hPr hP
    have hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)) :=
      fun a ha h0 => GlobalTheory.TopStep.intAt_div_of_redP hdu.2 ha h0
    have hred : ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (k x) = redV P.1 x := by
      have h1 := GlobalTheory.TopStep.redGL_of_prinCong (by omega : 0 < cst.D P) hkC
      intro x hx
      have h2 := GlobalTheory.TopStep.redV_redGL κ hx
      rw [h1, Units.val_one, Matrix.one_mulVec] at h2
      exact h2
    have hh := hL.stabG j b P hP
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe cst.sharp j P.1 hP hd (L.h j b P) hh k hkG hred, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    have hh' := hh
    unfold lamYat at hh'
    rw [if_pos hP] at hh'
    have hcong := GlobalTheory.CongLevel.conj_cong (qOf P.1) _ _ (L.h j b P) hh'
      (GlobalTheory.CongLevel.extE_cong P.1 (qOf P.1) (cOf R j) (fun i => i + 1) hd k hkG hred)
    have h1 := GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one Ch mu cst.sharp j P.1 hP ((qOf P.1 : X.E)⁻¹ •
      (((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P : AutY X R j).toLinearMap - LinearMap.id))
      fun x hx => by
        have hx' := hx
        unfold lamYat at hx' ⊢
        rw [if_pos hP] at hx' ⊢
        have h2 := hcong x hx'
        rw [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
        exact h2
    rw [smul_inv_smul₀ hq, add_sub_cancel] at h1
    unfold chiInv
    rw [h1, hψ, inv_one, one_mul]
  · have hstd : ∀ x, x ∈ lamYat (Pr := Pr) (R := R) j P.1 ↔ x ∈ stdAt X.E (R.N j + cOf R j) P.1 := by
      intro x
      unfold lamYat
      rw [if_neg hP]
      unfold LocE.lamY
      rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.TopStep.mem_stdAt]
      simp only [LocE.scE, Pi.zero_apply, Nat.cast_zero, ite_self, zpow_zero, inv_one, one_mul]
    have hbd := hL.boundQ j b P hP
    have hbd' : ∀ x ∈ stdAt X.E (R.N j + cOf R j) P.1, (L.h j b P)⁻¹ x ∈ stdAt X.E (R.N j + cOf R j) P.1 ∧
        ((qOf P.1 : X.E) ^ j) • (L.h j b P) x ∈ stdAt X.E (R.N j + cOf R j) P.1 := fun x hx => by
      have h1 := hbd x ((hstd x).2 hx)
      exact ⟨(hstd _).1 h1.1, (hstd _).1 h1.2⟩
    have hjD : j + 1 ≤ cst.D P := by
      have h1 := hL.depthQ' P hP
      have h2 := hL.hm
      omega
    have hg := GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q P.1 (cOf R j) j (cst.D P) (L.h j b P) κ hkC hjD hbd'
    have hginv := GlobalTheory.T.conj_extend_principalCongruence_cong_one_mod_q P.1 (cOf R j) j (cst.D P) (L.h j b P) κ⁻¹ (inv_mem hkC) hjD hbd'
    have einv : ((L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) κ.1 * L.h j b P)⁻¹ =
        (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) (κ⁻¹).1 * L.h j b P := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, GlobalTheory.CongLevel.extE_inv, mul_assoc]
      rfl
    refine ⟨GlobalTheory.CongLevel.extE (cOf R j) k, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ k, ?_⟩, GlobalTheory.CongLevel.extE_inX _ k, ?_⟩
    · have e : (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) =
          (L.h j b P)⁻¹ * GlobalTheory.CongLevel.extE (cOf R j) k * L.h j b P := by simp
      show (MulAut.conj (L.h j b P)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R j) k) ∈ Jat (Pr := Pr) cst.sharp j P.1
      rw [e]
      unfold Jat
      rw [if_neg hP]
      refine GlobalTheory.T.mem_parahoric_of_cong_one_mod_q P.1 (R.k + j) (R.N j) (cOf R j) _ hg ?_
      rw [einv]
      exact hginv
    · unfold chiInv
      rw [hψ, inv_one, one_mul]
      unfold lamRow
      rw [if_neg hP]
      exact GlobalTheory.T.blockDetResidueChar_eq_one_of_cong_mod_q P.1 _ (R.k + j) (R.N j) (R.N j + cOf R j) _ (by omega) hg

end GlobalTheory.LevOne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelLevelCharEqOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruentOne_mem_stepLevel_levelChar_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  first | exact @GlobalTheory.LevOne.cong_mem_level_chr_one | exact GlobalTheory.LevOne.cong_mem_level_chr_one | (intros; apply GlobalTheory.LevOne.cong_mem_level_chr_one <;> assumption)
end
