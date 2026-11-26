module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.ChainTwOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemVGsOfMemQE

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedDatumNeZeroIffDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedDatumNeZeroIffDoubleCoset
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Classical GlobalTheory.QNormal GlobalTheory.UnfoldLaw

noncomputable section

namespace GlobalTheory.SrcDoubleCoset

section Local

open Proof.NormalFormAtPrime Proof.boxSum_ne_zero_invariant_affineChange

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} {n' c' n c : ℕ}

theorem unfold_change₂ [CharZero K] (hP : IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {psi : E → K} {D : ℕ}
    (hD : 1 ≤ D) (hpsi : CharTo P D psi) (H : AddSubgroup ((Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)))
    (hq : ∀ z ∈ H, (qOf P : E) • z ∈ H) {m : ℕ} (hb : ∀ z ∈ H, IntHom P ((qOf P : E) ^ m • z))
    (hb' : ∀ z, IntHom P z → (qOf P : E) ^ m • z ∈ H) (hch : ∀ z ∈ H, IntAt P ((qOf P : E) ^ D * Loc.chArg z))
    {Psi₁ Psi₂ : Loc.SF E K (n' + c') (n + c)} (hs₁ : ∀ y, Psi₁ y ≠ 0 → y ∈ H) (hs₂ : ∀ y, Psi₂ y ≠ 0 → y ∈ H)
    (hi : ∀ y, ∀ z ∈ H, Psi₁ (y + (qOf P : E) • z) = Psi₁ y)
    (σ : ((Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) →ₗ[E] ((Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)))
    (hH : ∀ z, σ z ∈ H ↔ z ∈ H) {a b : K} (law : ∀ y, Psi₁ (σ y) * a = b * Psi₂ y)
    {xj xj' : (Fin n' → E) →ₗ[E] (Fin n → E)} (T : (Loc.FC n' c' n c → E) ≃ (Loc.FC n' c' n c → E))
    (hT : ∀ t, σ (Loc.xx1 xj t) = Loc.xx1 xj' (T t)) {d : E}
    (hd : ∀ t, Loc.chArg (σ (Loc.xx1 xj t)) = Loc.chArg (Loc.xx1 xj t) + d) {A B : ℕ} (hA : m ≤ A) (hB : m + D ≤ B) (wt : K) :
    Loc.E1 psi (LocE.valsQ E (qOf P) A B) wt Psi₁ xj' * a =
      (psi d)⁻¹ * b * Loc.E1 psi (LocE.valsQ E (qOf P) A B) wt Psi₂ xj := by
  have q0 := qOf_ne_zero P
  have hqk : ∀ k : ℕ, ∀ z ∈ H, (qOf P : E) ^ k • z ∈ H := fun k z hz => by
    induction k with
    | zero => simpa using hz
    | succ k ih => rw [pow_succ', mul_smul]; exact hq _ ih
  have hneg : ∀ {u : E}, IntAt P ((qOf P : E) ^ D * u) → IntAt P ((qOf P : E) ^ D * -u) := fun h => by
    simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h
  have hpt : ∀ t, integrand psi Psi₁ xj' (T t) * a = (psi d)⁻¹ * b * integrand psi Psi₂ xj t := by
    intro t
    unfold integrand
    rw [← hT, mul_right_comm, law]
    by_cases h0 : Psi₂ (Loc.xx1 xj t) = 0
    · simp [h0]
    have a1 := hch _ (hs₂ _ h0)
    have a2 := hch _ ((hH _).2 (hs₂ _ h0))
    rw [hd] at a2 ⊢
    have a3 : IntAt P ((qOf P : E) ^ D * d) := by
      convert a2.add (hneg a1) using 1
      ring
    have a4 := hpsi.1 _ _ a3 (hneg a3)
    rw [add_neg_cancel, hpsi.2 0 (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P)] at a4
    rw [neg_add, hpsi.1 _ _ (hneg a1) (hneg a3), ← eq_inv_of_mul_eq_one_right a4.symm]
    ring
  have hsupp : ∀ Ψ : Loc.SF E K (n' + c') (n + c), (∀ y, Ψ y ≠ 0 → y ∈ H) →
      ∀ y t, integrand psi Ψ y t ≠ 0 → t ∈ lat P (Loc.FC n' c' n c) ((qOf P : E) ^ A) := fun Ψ hs y t h p => by
    have := (intHom_iff _).1 (hb _ (hs _ (left_ne_zero_of_mul h))) p.1.2 p.1.1
    rw [LinearMap.smul_apply, Pi.smul_apply, Proof.unipotentRadicals_act_affine_unfoldingSpaces.unfoldingAffineLinearMap_apply_freeEntry] at this
    exact intAt_pow_mono hA this
  let M : AddSubgroup (Loc.FC n' c' n c → E) :=
    H.comap (((qOf P : E) ^ D)⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E))).toAddMonoidHom
  have mM : ∀ u, u ∈ M ↔ ((qOf P : E) ^ D)⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) u ∈ H :=
    fun u => Iff.rfl
  have key := sum_reps_equiv (M₀ := lat P (Loc.FC n' c' n c) ((qOf P : E) ^ B)⁻¹) (M := M)
    (M₁ := lat P (Loc.FC n' c' n c) ((qOf P : E) ^ A)) (Fintype.piFinset fun _ => LocE.valsQ E (qOf P) A B)
    (fun u hu => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hB
      have h1 : IntHom P (((qOf P : E) ^ (m + D + k))⁻¹ • Proof.unipotentRadicals_act_affine_unfoldingSpaces.linPart (0 : (Fin n' → E) →ₗ[E] (Fin n → E)) u) :=
        (intHom_iff _).2 fun s l => by
          rw [LinearMap.smul_apply, Pi.smul_apply, linPart_single, smul_eq_mul]
          split_ifs
          · exact hu _
          · simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
      rw [mM]
      convert hqk k _ (hb' _ h1) using 1
      rw [smul_smul, smul_smul]
      congr 1
      field_simp
      ring)
    (fun u hu p => by
      have := (intHom_iff _).1 (hb _ (hqk D _ ((mM u).1 hu))) p.1.2 p.1.1
      rw [smul_inv_smul₀ (pow_ne_zero _ q0), LinearMap.smul_apply, Pi.smul_apply, linPart_single, dite_eq_left p.2] at this
      exact intAt_pow_mono hA this)
    (fun s hs s' hs' h => funext fun i => (Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP A B).1 _ (Fintype.mem_piFinset.1 hs i) _
      (Fintype.mem_piFinset.1 hs' i) (h i))
    (fun v hv => by
      choose s hs hs' using fun i => (Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP A B).2 (v i) (hv i)
      exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩)
    T (fun s t => by
      rw [mM, mM, ← affineFreeParam_first_sub_eq_linearPart xj', ← affineFreeParam_first_sub_eq_linearPart xj, ← hT, ← hT, ← map_sub, ← map_smul, hH])
    (fun t => integrand psi Psi₁ xj' t * a)
    (fun t u hu => by
      obtain ⟨z, hz, e⟩ : ∃ z ∈ H, Loc.xx1 xj' (t + u) = Loc.xx1 xj' t + (qOf P : E) ^ D • z :=
        ⟨_, (mM u).1 hu, by rw [smul_inv_smul₀ (pow_ne_zero _ q0), ← sub_eq_iff_eq_add', affineFreeParam_first_sub_eq_linearPart, add_sub_cancel_left]⟩
      unfold integrand
      rw [e]
      generalize Loc.xx1 xj' t = y
      have e1 : Psi₁ (y + (qOf P : E) ^ D • z) = Psi₁ y := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hD
        rw [pow_add, pow_one, mul_smul, hi _ _ (hqk d z hz)]
      rw [e1]
      by_cases h0 : Psi₁ y = 0
      · simp [h0]
      have a1 := IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg (hch _ hz)
      rw [chArg_add_smul, neg_add, hpsi.1 _ _ (hneg (hch _ (hs₁ _ h0))) (intAt_pow_mul D a1), hpsi.2 _ a1, mul_one])
    (fun t h => hsupp Psi₁ hs₁ _ t (left_ne_zero_of_mul h))
    (fun t h => hsupp Psi₂ hs₂ xj t (right_ne_zero_of_mul (hpt t ▸ h)))
  simp only [hpt] at key
  rw [← Finset.mul_sum, ← Finset.sum_mul] at key
  unfold Loc.E1
  unfold integrand at key
  rw [mul_assoc, ← key]
  ring

end Local

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem mem_moved {i : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h : AutY X R (i + 1)}
    (hh : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P)) (z : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    z ∈ movedHom (lamYat (Pr := Pr) (R := R) i P) (lamYat (Pr := Pr) (R := R) (i + 1) P) (1 : AutY X R i) h ↔
      ∀ v ∈ lamYat (Pr := Pr) (R := R) i P, z v ∈ lamYat (Pr := Pr) (R := R) (i + 1) P := by
  constructor
  · intro hz v hv
    have h1 : h.symm (z v) ∈ lamYat (Pr := Pr) (R := R) (i + 1) P := hz v hv
    have h2 := (hh (h.symm (z v))).2 h1
    rwa [LinearEquiv.apply_symm_apply] at h2
  · intro hz v hv
    show h.symm (z v) ∈ _
    exact (inv_mem hh (z v)).2 (hz v hv)

theorem intAt_chArg_G {i : ℕ} (hi : i + 2 ≤ R.m) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (z : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)))
    (hz : ∀ v ∈ lamYat (Pr := Pr) (R := R) i P, z v ∈ lamYat (Pr := Pr) (R := R) (i + 1) P) :
    IntAt P ((qOf P : X.E) * Loc.chArg z) := by
  have hc : cOf R i = cOf R (i + 1) + 1 := by unfold cOf; omega
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ _ fun s hs => ?_
  have hs := Finset.mem_range.1 hs
  have l1 : R.N (i + 1) + s < R.N (i + 1) + cOf R (i + 1) := by omega
  have l2 : R.N i + s + 1 < R.N i + cOf R i := by omega
  unfold Loc.atN
  rw [dite_eq_left l1, Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.eN_eq_single l2]
  have h1 := hz
  unfold lamYat at h1
  simp only [if_pos hP] at h1
  have h2 := LastSteps.mem_homS_sclLat.1 h1 ⟨_, l1⟩ ⟨_, l2⟩
  have e : LocE.scE (R.N i) (fun i => i + 1) (R.N i + s + 1) - LocE.scE (R.N (i + 1)) (fun i => i + 1) (R.N (i + 1) + s) = 1 := by
    unfold LocE.scE
    rw [if_neg (by omega), if_neg (by omega)]
    dsimp only
    omega
  rw [e, zpow_one, mul_comm] at h2
  exact h2

end Chain

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}

theorem unfoldedDatum_ne_zero_of_doubleCoset_source (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2)
    (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) {a₁ a₂ : AutY X R i} {h : AutY X R (i + 1)}
    (ha₁ : a₁ ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1)) (ha₂ : a₂ ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1))
    (hh : h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1)) {r κ : AutY X R i}
    (hr : r ∈ Loc.R1 X.E (R.N i) (cOf R i)) (hκ : κ ∈ Jat (Pr := Pr) cst.sharp i P.1) (e : a₂ = r * a₁ * κ)
    (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P a₂ h) : FiniteSumNonzeroLargeDepth Ch sel mu cst i P a₁ h := by
  have hm := hL.hm
  have hc : 1 ≤ cOf R (i + 1) := by unfold cOf; omega
  have hc' : cOf R i = cOf R (i + 1) + 1 := by unfold cOf; omega
  have hok := hL.cst_ok
  have hP1 := UnfoldTwoSided.degOne_bad hX hPr hsel P
  have hD1 := hL.depthG P hP
  have hκs : κ ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) := jat_le _ _ _ hκ
  have hrs : r ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) := by
    have e' : r = a₂ * κ⁻¹ * a₁⁻¹ := by rw [e]; group
    rw [e']
    exact mul_mem (mul_mem ha₂ (inv_mem hκs)) (inv_mem ha₁)
  subst e

  have hmu : ∀ {j : ℕ} {g : AutY X R j}, g ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P.1) →
      muAt Ch sel mu cst i P ((LinearEquiv.det g : X.Eˣ) : X.E) ≠ 0 := by
    intro j g hg
    have hu : IsUnit (redP P.1 ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
      unfold lamYat at hg
      rw [if_pos hP] at hg
      exact LastSteps.isUnit_det_of_stab hg
    unfold muAt
    rw [LastSteps.locChar_unit _ _ hu]
    unfold LocE.unitV
    rw [dite_eq_left hu]
    exact Units.ne_zero _
  have hsq : cst.sq P ≠ 0 := by
    intro e0
    have := hok.sq_sq P
    rw [e0, zero_pow two_ne_zero] at this
    exact hP1.1.ne_zero (by exact_mod_cast this.symm)
  have hS₁ : omScal Ch sel mu cst i P a₁ h ≠ 0 := by
    unfold omScal
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hmu ha₁) (inv_ne_zero (hmu hh))) (zpow_ne_zero _ hsq)) (zpow_ne_zero _ hsq)
  have hb0 : omScal Ch sel mu cst i P a₁ h * muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E) ≠ 0 :=
    mul_ne_zero hS₁ (hmu hκs)
  have hpd : cst.psi P (Loc.n1Arg r) ≠ 0 := by
    have hint : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * Loc.n1Arg r) := by
      rw [hD1, pow_one]
      have hr' := hrs
      unfold lamYat at hr'
      rw [if_pos hP] at hr'
      exact Mem.LevFin.intAt_n1Arg_G (Proof.NormalFormAtPrime.qOf_ne_zero _) r hr'
    exact left_ne_zero_of_mul ((Mem.Col2.IdxEx.psi_mul_neg (Mem.Col2.IdxEx.charTo hok P) hint).trans_ne one_ne_zero)

  obtain ⟨m, hb, hb'⟩ : ∃ m : ℕ,
      (∀ z ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h,
        IntHom P.1 ((qOf P.1 : X.E) ^ m • z)) ∧ ∀ z, IntHom P.1 z → (qOf P.1 : X.E) ^ m • z ∈
          movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h :=
    movedHom_bdd _ _ 1 h
  obtain ⟨hs, hinv⟩ := phiAt_mod Ch mu cst.sharp (i := i) (by omega) P.1
  have supp : ∀ {a : AutY X R i}, a ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → ∀ y, omPhi Ch sel mu cst i P a h y ≠ 0 →
      y ∈ movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h := by
    intro a ha y hy
    rw [mem_moved hh]
    intro v hv
    rw [omPhi_eq] at hy
    have h1 := hs _ (right_ne_zero_of_mul hy) (a⁻¹ v) ((inv_mem ha v).2 hv)
    change h.symm (y (a (a⁻¹ v))) ∈ _ at h1
    rw [show a (a⁻¹ v) = v from LinearEquiv.apply_symm_apply a v] at h1
    have h2 := (hh _).2 h1
    rwa [LinearEquiv.apply_symm_apply] at h2
  refine ⟨max H.choose m, max H.choose_spec.choose (m + cst.D P), fun A B hA hB => ?_⟩
  obtain ⟨xj, hx⟩ := Function.ne_iff.1 (H.choose_spec.choose_spec A B (le_of_max_le_left hA) (le_of_max_le_left hB))
  obtain ⟨g, hg⟩ := exists_res hr
  obtain ⟨T, hT⟩ := UnfoldTwoSided.exists_move_right hc hc' hr hg xj
  have key := unfold_change₂ (K := X.K) hP1 (n' := R.N i) (c' := cOf R i) (n := R.N (i + 1)) (c := cOf R (i + 1))
    (hok.D_pos P) (Mem.Col2.IdxEx.charTo hok P)
    (movedHom (lamYat (Pr := Pr) (R := R) i P.1) (lamYat (Pr := Pr) (R := R) (i + 1) P.1) (1 : AutY X R i) h)
    (fun z hz => by
      rw [mem_moved hh] at hz ⊢
      intro v hv
      rw [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hz v hv) _)
    hb hb'
    (fun z hz => by
      rw [hD1, pow_one]
      exact intAt_chArg_G (by omega) hP z ((mem_moved hh z).1 hz))
    (Psi₁ := omPhi Ch sel mu cst i P a₁ h) (Psi₂ := omPhi Ch sel mu cst i P (r * a₁ * κ) h)
    (supp ha₁) (supp ha₂)
    (fun y z hz => by
      rw [omPhi_eq, omPhi_eq, ← hinv (h.symm.toLinearMap ∘ₗ y ∘ₗ a₁.toLinearMap) (h.symm.toLinearMap ∘ₗ z ∘ₗ a₁.toLinearMap)
        (fun v hv => (inv_mem hh _).2 ((mem_moved hh z).1 hz (a₁ v) ((ha₁ v).2 hv))),
        LinearMap.add_comp, LinearMap.comp_add, LinearMap.smul_comp, LinearMap.comp_smul])
    (LinearMap.lcomp X.E _ r.toLinearMap)
    (fun z => by
      rw [mem_moved hh, mem_moved hh]
      constructor
      · intro hz v hv
        have := hz (r⁻¹ v) ((inv_mem hrs v).2 hv)
        change z (r (r⁻¹ v)) ∈ _ at this
        rwa [show r (r⁻¹ v) = v from LinearEquiv.apply_symm_apply r v] at this
      · intro hz v hv
        exact hz (r v) ((hrs v).2 hv))
    (a := omScal Ch sel mu cst i P (r * a₁ * κ) h * lamRow Ch mu cst.sharp i P.1 κ.toLinearMap)
    (b := omScal Ch sel mu cst i P a₁ h * muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E))
    (fun y => by
      have := DatumLaw.phiAt_source Ch sel mu cst cst.sharp (by omega) P hκ
        (h.symm.toLinearMap ∘ₗ (LinearMap.lcomp X.E _ r.toLinearMap y) ∘ₗ a₁.toLinearMap)
      have e2 : h.symm.toLinearMap ∘ₗ y ∘ₗ (r * a₁ * κ).toLinearMap =
          (h.symm.toLinearMap ∘ₗ (LinearMap.lcomp X.E _ r.toLinearMap y) ∘ₗ a₁.toLinearMap) ∘ₗ κ.toLinearMap :=
        LinearMap.ext fun v => rfl
      rw [omPhi_eq, omPhi_eq, e2]
      linear_combination (-(omScal Ch sel mu cst i P a₁ h * omScal Ch sel mu cst i P (r * a₁ * κ) h)) * this)
    T hT (d := Loc.n1Arg r) (fun t => UnfoldTwoSided.chArg_right hc hc' hr.1 xj t)
    (A := A) (B := B) (le_of_max_le_right hA) (le_of_max_le_right hB) (((qOf P.1 : X.K) ^ B)⁻¹)
  refine Function.ne_iff.2 ⟨xj ∘ₗ g.toLinearMap, fun h0 => hx ?_⟩
  have h0' : Loc.E1 (cst.psi P) (LocE.valsQ X.E (qOf P.1) A B) (((qOf P.1 : X.K) ^ B)⁻¹) (omPhi Ch sel mu cst i P a₁ h)
      (xj ∘ₗ g.toLinearMap) = 0 := h0
  rw [h0', zero_mul] at key
  have := (mul_eq_zero.1 key.symm).resolve_left (mul_ne_zero (inv_ne_zero hpd) hb0)
  exact this

end Main

theorem unfoldedDatum_ne_zero_iff_doubleCoset' : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → cst.sharp = true → L.Ok Ch sel mu cst G m2 → ∀ i, i < m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)), hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) → SameDC (Pr := Pr) cst.sharp i P.1 1 hal → (FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h ↔ FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h) := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr _ hsel _ hL i hi P hP hal h hal_st h_st hdc
  obtain ⟨r, hr, κ, hκ, e⟩ := hdc
  constructor
  · exact unfoldedDatum_ne_zero_of_doubleCoset_source hX hPr hsel hL hi P hP (one_mem _) hal_st h_st hr hκ e
  · exact unfoldedDatum_ne_zero_of_doubleCoset_source hX hPr hsel hL hi P hP hal_st (one_mem _) h_st (inv_mem hr) (inv_mem hκ) (by rw [e]; group)

end GlobalTheory.SrcDoubleCoset
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedDatumNeZeroIffDoubleCosetStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → cst.sharp = true → L.Ok Ch sel mu cst G m2 → ∀ i, i < m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → ∀ (hal : AutY X R i) (h : AutY X R (i + 1)), hal ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) i P.1) → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) (i + 1) P.1) → SameDC (Pr := Pr) cst.sharp i P.1 1 hal → (FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h ↔ FiniteSumNonzeroLargeDepth Ch sel mu cst i P 1 h) := by
  first | exact @GlobalTheory.SrcDoubleCoset.unfoldedDatum_ne_zero_iff_doubleCoset' | exact GlobalTheory.SrcDoubleCoset.unfoldedDatum_ne_zero_iff_doubleCoset' | (intros; apply GlobalTheory.SrcDoubleCoset.unfoldedDatum_ne_zero_iff_doubleCoset' <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoubleCosetRepsConjugateLevelGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoubleCosetRepsConjugateLevelGroups
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Classical

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem cbe_iff {k : Type} [CommRing k] {n c : ℕ} (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)))
    {r h' κ s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.R1 k n c) (hκ : κ ∈ J) :
    s ∈ Loc.Cbe J (r * h' * κ) ↔ r⁻¹ * s * r ∈ Loc.Cbe J h' := by
  constructor
  · rintro ⟨hs1, hs2⟩
    refine ⟨(Loc.R1 k n c).mul_mem ((Loc.R1 k n c).mul_mem ((Loc.R1 k n c).inv_mem hr) hs1) hr, ?_⟩
    have h2 : (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ ∈ J := hs2
    show h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ ∈ J
    have e : h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ = κ * ((r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹) * κ⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hκ h2) (inv_mem hκ)
  · rintro ⟨hs1, hs2⟩
    have hs1' : s ∈ Loc.R1 k n c := by
      have := (Loc.R1 k n c).mul_mem ((Loc.R1 k n c).mul_mem hr hs1) ((Loc.R1 k n c).inv_mem hr)
      rwa [show r * (r⁻¹ * s * r) * r⁻¹ = s by group] at this
    refine ⟨hs1', ?_⟩
    have h2 : h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹ ∈ J := hs2
    show (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ ∈ J
    have e : (r * h' * κ)⁻¹ * s * (r * h' * κ)⁻¹⁻¹ = κ⁻¹ * (h'⁻¹ * (r⁻¹ * s * r) * h'⁻¹⁻¹) * κ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hκ) h2) hκ

theorem red_conj {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (δ : GLint E n P) {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ GLint E n P) {A : GL (Fin n) (𝓞 E ⧸ P.asIdeal)}
    (hA : ∀ y ∈ stdAt E n P, redV P (g y) = A.1.mulVec (redV P y)) :
    ∀ y ∈ stdAt E n P, redV P ((δ.1 * g * δ.1⁻¹) y) =
      (GlobalTheory.TopStep.redGL n P δ * A * (GlobalTheory.TopStep.redGL n P δ)⁻¹).1.mulVec (redV P y) := by
  intro y hy
  have h1 : δ.1⁻¹ y ∈ stdAt E n P := ((δ⁻¹).2 y).2 hy
  have h2 : g (δ.1⁻¹ y) ∈ stdAt E n P := (hg _).2 h1
  show redV P (δ.1 (g (δ.1⁻¹ y))) = _
  rw [GlobalTheory.TopStep.redV_redGL δ h2, hA _ h1]
  have h3 := GlobalTheory.TopStep.redV_redGL δ⁻¹ hy
  have e : (δ⁻¹).1 y = δ.1⁻¹ y := rfl
  rw [e] at h3
  rw [h3, map_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end GlobalTheory.Mem.Col2.IdxEx.LocMatch

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem inX_mem_lamYat_iff {X : Fields} {Pr : Primes X} {R : Ranks} (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ Pr.vGs) (x : Sp X.E (R.N j)) :
    Loc.inX X.E (R.N j) (cOf R j) x ∈ lamYat (Pr := Pr) (R := R) j P ↔ x ∈ stdAt X.E (R.N j) P := by
  unfold lamYat
  rw [if_pos hP]
  exact ⟨fun hx => by simpa only [GlobalTheory.CongLevel.resX_inX] using GlobalTheory.CongLevel.resX_mem P _ _ _ _ hx,
    GlobalTheory.CongLevel.inX_mem_lamY P _ _ _ x⟩

theorem lamRow_tup {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ}
    (mu mu' : Tup X.F X.E X.K S) (j : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (f : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j)) :
    lamRow Ch mu true j P f = lamRow Ch mu' true j P f := by
  unfold lamRow
  simp only [if_pos hP, if_true]

end GlobalTheory.Mem.Col2.IdxEx.LocMatch

namespace GlobalTheory.Mem.Col2.IdxEx.LocMatch

theorem loc_match : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu mu' : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (cst' : LocCst X (rowSG Pr sel mu')) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (L' : ChIdx X Pr R (QE sel (mu' : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → cst.sharp = true → cst'.sharp = true → L.Ok Ch sel mu cst G m2 → L'.Ok Ch sel mu' cst' G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (b' : L'.β j) (w : {w // w ∈ Pr.vGs}) (r κ : AutY X R j), r ∈ Loc.R1 X.E (R.N j) (cOf R j) → κ ∈ Jat (Pr := Pr) true j w.1 → L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ → ∃ x : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), (r = 1 → x = 1) ∧ (∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), hbar ∈ (L.levG j b w).H ↔ x * hbar * x⁻¹ ∈ (L'.levG j b' w).H) ∧ ∀ (hbar : ↥(L.levG j b w).H) (hbar' : ↥(L'.levG j b' w).H), hbar'.1 = x * hbar.1 * x⁻¹ → (L.levG j b w).lam hbar = (L'.levG j b' w).lam hbar' := by
  intro X Pr R Ch sel S mu mu' cst cst' L L' G m2 _ _ _ hs hs' hok hok' j hj b b' w r κ hr hκ he
  have hP : w.1 ∈ Pr.vGs := w.2
  have hjm : j < R.m := by rw [hok.hm]; omega
  have hG := hok.grpG j b w
  have hG' := hok'.grpG j b' w
  have hC := hok.chrG j b w
  have hC' := hok'.chrG j b' w
  have hint := hok.int j b ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hint' := hok'.int j b' ⟨w.1, Finset.mem_union_left _ w.2⟩
  have hst := hok.stabG j b ⟨w.1, Finset.mem_union_left _ w.2⟩ hP
  have hst' := hok'.stabG j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ hP
  have hpsi := fun a ha => hok.psi0 ⟨w.1, Finset.mem_union_left _ w.2⟩ a hP ha
  have hpsi' := fun a ha => hok'.psi0 ⟨w.1, Finset.mem_union_left _ w.2⟩ a hP ha
  rw [hs] at hG hC hint
  rw [hs'] at hG' hC' hint'
  unfold chiInv at hC hC'
  rw [hs] at hC
  rw [hs'] at hC'
  generalize L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = h at hG hC hint hst he
  generalize L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ = h' at hG' hC' hint' hst' he
  subst he

  have hκs := jat_le_stab_lamY true j w.1 hP κ hκ
  have hrs : r ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j w.1) := by
    have := mul_mem (mul_mem hst (inv_mem hκs)) (inv_mem hst')
    rwa [show r * h' * κ * κ⁻¹ * h'⁻¹ = r by group] at this
  obtain ⟨γ, hγ⟩ := GlobalTheory.QNormal.exists_res hr
  have hγint : γ ∈ GLint X.E (R.N j) w.1 := by
    intro y
    rw [← inX_mem_lamYat_iff (Pr := Pr) j hP, ← inX_mem_lamYat_iff (Pr := Pr) j hP, ← hγ y]
    exact hrs _
  set γg : GLint X.E (R.N j) w.1 := ⟨γ, hγint⟩ with hγg
  refine ⟨GlobalTheory.TopStep.redGL (R.N j) w.1 γg⁻¹, ?_, ?_, ?_⟩
  · intro h1
    subst h1
    have e : γ = 1 := by
      refine LinearEquiv.ext fun y => GlobalTheory.QNormal.inX_injective (c := cOf R j) ?_
      rw [← hγ y]
      rfl
    have e2 : γg = 1 := Subtype.ext e
    rw [e2, inv_one, map_one]
  · intro hbar
    rw [hG, hG']
    constructor
    · rintro ⟨g, ⟨r₁, hr₁, hres⟩, hred⟩
      refine ⟨γ⁻¹ * g * γ, ⟨r⁻¹ * r₁ * r, (cbe_iff _ hr hκ).1 hr₁, GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ hres⟩, ?_⟩
      intro y hy
      exact red_conj γg⁻¹ (hint ⟨r₁, hr₁, hres⟩) hred y hy
    · rintro ⟨g', ⟨r₁', hr₁', hres'⟩, hred'⟩
      have hγ' : ∀ y, r⁻¹ (Loc.inX X.E (R.N j) (cOf R j) y) = Loc.inX X.E (R.N j) (cOf R j) (γ⁻¹ y) := by
        intro y
        show r.symm _ = _
        rw [LinearEquiv.symm_apply_eq, hγ]
        show _ = Loc.inX X.E (R.N j) (cOf R j) (γ (γ.symm y))
        rw [LinearEquiv.apply_symm_apply]
      have hmem : r * r₁' * r⁻¹ ∈ Loc.Cbe (Jat (Pr := Pr) true j w.1) (r * h' * κ) := by
        refine (cbe_iff _ hr hκ).2 ?_
        rwa [show r⁻¹ * (r * r₁' * r⁻¹) * r = r₁' by group]
      refine ⟨γ * g' * γ⁻¹, ⟨r * r₁' * r⁻¹, hmem, fun y => GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ' hres' y⟩, ?_⟩
      intro y hy
      have e : ∀ (Q A : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)), Q * (Q⁻¹ * A * Q⁻¹⁻¹) * Q⁻¹ = A := by
        intro Q A
        group
      have := red_conj γg (hint' ⟨r₁', hr₁', hres'⟩) hred' y hy
      rw [map_inv, e] at this
      exact this
  · intro hbar hbar' hx
    obtain ⟨g, ⟨r₁, hr₁, hres⟩, hred⟩ := (hG hbar.1).1 hbar.2
    have hgint := hint ⟨r₁, hr₁, hres⟩
    have hr₁' := (cbe_iff _ hr hκ).1 hr₁
    have hres' := GlobalTheory.Proof.level_eq_parahoric_category.conj_res hγ hres
    have hred' : ∀ y ∈ stdAt X.E (R.N j) w.1, redV w.1 ((γ⁻¹ * g * γ) y) = hbar'.1.1.mulVec (redV w.1 y) := by
      intro y hy
      rw [hx]
      exact red_conj γg⁻¹ hgint hred y hy
    have e1 := hC hbar g r₁ hr₁ hres hred
    have e2 := hC' hbar' (γ⁻¹ * g * γ) (r⁻¹ * r₁ * r) hr₁' hres' hred'
    refine Units.ext ?_
    rw [e1, e2, GlobalTheory.Proof.level_eq_parahoric_category.n1Arg_conj_eq hr hr₁.1]

    have hr₁s : r₁ ∈ stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1) := by
      have h1 : (r * h' * κ)⁻¹ * r₁ * (r * h' * κ)⁻¹⁻¹ ∈ Jat (Pr := Pr) true j w.1 := hr₁.2
      have h2 := jat_le_stab_lamY true j w.1 hP _ h1
      have h3 := mul_mem (mul_mem hst h2) (inv_mem hst)
      rw [show r * h' * κ * ((r * h' * κ)⁻¹ * r₁ * (r * h' * κ)⁻¹⁻¹) * (r * h' * κ)⁻¹ = r₁ by group] at h3
      unfold lamYat at h3
      rw [if_pos hP] at h3
      exact h3
    have hq := GlobalTheory.TopStep.qOf_ne_zero (P := w.1) (E := X.E)
    have hia := GlobalTheory.Mem.LevFin.intAt_n1Arg_G hq r₁ hr₁s
    have ea : ((qOf w.1 : ℕ) : X.E) * Loc.n1Arg r₁ / ((qOf w.1 : ℕ) : X.E) = Loc.n1Arg r₁ := by
      field_simp
    have p1 := hpsi _ hia
    have p2 := hpsi' _ hia
    rw [ea] at p1 p2
    rw [p1, p2]
    congr 1

    rw [lamRow_tup Ch mu mu' j hP]
    have ht : h'⁻¹ * (r⁻¹ * r₁ * r) * h'⁻¹⁻¹ ∈ Jat (Pr := Pr) true j w.1 := hr₁'.2
    rw [inv_inv] at ht
    have e : (r * h' * κ)⁻¹ * r₁ * (r * h' * κ) = κ⁻¹ * (h'⁻¹ * (r⁻¹ * r₁ * r) * h') * κ := by group
    rw [e]
    generalize h'⁻¹ * (r⁻¹ * r₁ * r) * h' = t at ht ⊢
    have LM := GlobalTheory.SymLevelMul.lamRow_mul Ch mu' j w.1 hjm hP
    have hκi : κ⁻¹ ∈ Jat (Pr := Pr) (R := R) true j w.1 := inv_mem hκ
    rw [LM _ (mul_mem hκi ht) _ hκ, LM _ hκi _ ht]
    have e3 : lamRow Ch mu' true j w.1 t.toLinearMap =
        lamRow Ch mu' true j w.1 t.toLinearMap * lamRow Ch mu' true j w.1 (κ⁻¹ : AutY X R j).toLinearMap *
          lamRow Ch mu' true j w.1 κ.toLinearMap := by
      conv_lhs => rw [show t = t * κ⁻¹ * κ by group]
      rw [LM _ (mul_mem ht hκi) _ hκ, LM _ ht _ hκi]
    linear_combination -e3

end GlobalTheory.Mem.Col2.IdxEx.LocMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DoubleCosetRepsConjugateLevelGroupsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCoset_reps_conjugate_level_groups : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu mu' : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (cst' : LocCst X (rowSG Pr sel mu')) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (L' : ChIdx X Pr R (QE sel (mu' : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → Ch.Ok → cst.sharp = true → cst'.sharp = true → L.Ok Ch sel mu cst G m2 → L'.Ok Ch sel mu' cst' G m2 → ∀ (j : ℕ), j ≤ m2 + 1 → ∀ (b : L.β j) (b' : L'.β j) (w : {w // w ∈ Pr.vGs}) (r κ : AutY X R j), r ∈ Loc.R1 X.E (R.N j) (cOf R j) → κ ∈ Jat (Pr := Pr) true j w.1 → L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * L'.h j b' ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ → ∃ x : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), (r = 1 → x = 1) ∧ (∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal), hbar ∈ (L.levG j b w).H ↔ x * hbar * x⁻¹ ∈ (L'.levG j b' w).H) ∧ ∀ (hbar : ↥(L.levG j b w).H) (hbar' : ↥(L'.levG j b' w).H), hbar'.1 = x * hbar.1 * x⁻¹ → (L.levG j b w).lam hbar = (L'.levG j b' w).lam hbar' := by
  first | exact @GlobalTheory.Mem.Col2.IdxEx.LocMatch.loc_match | exact GlobalTheory.Mem.Col2.IdxEx.LocMatch.loc_match | (intros; apply GlobalTheory.Mem.Col2.IdxEx.LocMatch.loc_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjReferenceChartIndex
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

theorem pi_conj {X : Fields} {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ Λ' : LevFam X.E X.K n SG) (x : ∀ w : SG, GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal))
    (hH : ∀ w hbar, hbar ∈ (Λ w).H ↔ x w * hbar * (x w)⁻¹ ∈ (Λ' w).H)
    (hL : ∀ w (hbar : ↥(Λ w).H) (hbar' : ↥(Λ' w).H), hbar'.1 = x w * hbar.1 * (x w)⁻¹ →
      (Λ w).lam hbar = (Λ' w).lam hbar') :
    (∀ g : GLG (E := X.E) (n := n) (SG := SG), g ∈ Λ.grp ↔ (fun w => x w * g w * (x w)⁻¹) ∈ Λ'.grp) ∧
    ∀ (g : ↥Λ.grp) (g0 : ↥Λ'.grp), (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) → Λ.chr g = Λ'.chr g0 := by
  refine ⟨fun g => ?_, fun g g0 hg => ?_⟩
  · simp only [LevFam.grp, Subgroup.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun w => hH w (g w)
  · rw [LevFam.chr_apply, LevFam.chr_apply]
    exact Finset.prod_congr rfl fun w _ => hL w _ _ (hg w)

section Gen

variable {Xf : Fields} {Pr : Primes Xf} {R : Ranks} {Ch : Chars Xf Pr R.m}
  {sel : HeightOneSpectrum (𝓞 Xf.F) → HeightOneSpectrum (𝓞 Xf.E)} {S : Set ℕ} {mu : Tup Xf.F Xf.E Xf.K S}
  {cst : LocCst Xf (rowSG Pr sel mu)} {L : ChIdx Xf Pr R (QE sel (mu : Chr Xf.F Xf.E Xf.K))} {G : ChGlob Xf R.m} {m2 : ℕ}

theorem cosetOne (hX : Xf.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel Xf sel) (hs : cst.sharp = true)
    (hok : L.Ok Ch sel mu cst G m2) : ∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
      SameDC (Pr := Pr) true j P.1 1 (L.h j b P) := by
  have hB := clL_base hok hX hPr hCh hs
  intro j
  induction j with
  | zero =>
    intro _ b P _
    rw [hok.zero_h]
    exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  | succ i ih =>
    intro hj b P hP
    by_cases hi : i < m2
    · obtain ⟨al, hal⟩ := hok.nonvan i hi b P
      have h1 := ih (by omega) al P hP
      have hs1 := hok.stabG i al P hP
      have hs2 := hok.stabG (i + 1) b P hP
      have h2 := (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G m2 hX hPr hCh hsel hs hok i hi P hP _ _ hs1 hs2 (by rw [hs]; exact h1)).1 hal
      have h3 := twSurjG G.σ₀ hB hi P hP _ hs2 h2
      rwa [hs] at h3
    · obtain rfl : i = m2 := by omega
      rw [hok.last_h]
      exact ⟨1, one_mem _, 1, one_mem _, by simp⟩

theorem idx_nonempty (hX : Xf.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel Xf sel) (hs : cst.sharp = true)
    (hok : L.Ok Ch sel mu cst G m2) (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) :
    ∀ j, j ≤ m2 + 1 → Nonempty (L.β j) := by
  have hB := clL_base hok hX hPr hCh hs
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨b, -⟩ := hok.zero_uniq
    exact ⟨b⟩
  | succ i ih =>
    intro hj
    by_cases hi : i < m2
    · obtain ⟨al⟩ := ih (by omega)
      obtain ⟨b, -⟩ := hok.surj i hi (fun _ => 1) (fun _ _ => one_mem _) (fun P hP => absurd (hQ P) hP)
        (fun P => ⟨al, (GlobalTheory.T.unfoldedDatum_ne_zero_iff_doubleCoset Ch sel mu cst L G m2 hX hPr hCh hsel hs hok i hi P (hQ P) _ _ (hok.stabG i al P (hQ P))
          (one_mem _) (by rw [hs]; exact cosetOne hX hPr hCh hsel hs hok i (by omega) al P (hQ P))).2
          (twNonVanG G.σ₀ hB hi P (hQ P))⟩)
      exact ⟨b⟩
    · obtain rfl : i = m2 := by omega
      obtain ⟨b, -⟩ := hok.last_uniq
      exact ⟨b⟩

end Gen

end GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch


open Classical in
theorem idx_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ b : Idx I.sel (I.tup a) (I.idx a) i, ∃ (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i)
      (x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal)),
      (i + 1 = B.R.m → ∀ w, x w = 1) ∧
      (∀ g : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs), g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp ↔
        (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp) ∧
      ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp),
        (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
        (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).chr g0 := by
  intro B X I h l a i hi1 hi b
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hoka := h.idx_ok a
  have hok0 := h.idx_ok I.mu0
  generalize B.R.m - 2 = m2 at hoka hok0
  have hm := hoka.hm
  have hQ0 : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P =>
    (Finset.mem_union.1 P.2).resolve_right (by
      have e : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
      rw [e]
      exact Finset.notMem_empty _)
  rcases b with ⟨_ | β, hb⟩
  · exact absurd (hb.2 hi) (by simp)
  have key : ∃ β0 : (I.idx I.mu0).β i, ∀ w : (B.primes X).vGs, ∃ (r κ : AutY B.fields B.R i),
      r ∈ Loc.R1 B.fields.E (B.R.N i) (cOf B.R i) ∧ κ ∈ Jat (Pr := B.primes X) true i w.1 ∧
      (I.idx a).h i β ⟨w.1, Finset.mem_union_left _ w.2⟩ = r * (I.idx I.mu0).h i β0 ⟨w.1, Finset.mem_union_left _ w.2⟩ * κ ∧
      (i + 1 = B.R.m → r = 1) := by
    by_cases hlast : i = m2 + 1
    · subst hlast
      obtain ⟨β0, -⟩ := hok0.last_uniq
      refine ⟨β0, fun w => ⟨1, 1, one_mem _, one_mem _, ?_, fun _ => rfl⟩⟩
      rw [hoka.last_h, hok0.last_h]
      simp
    · obtain ⟨β0⟩ := idx_nonempty hX l.pr h.ch_ok h.sel_ok (h.sharp I.mu0) hok0 hQ0 i (by omega)
      refine ⟨β0, fun w => ?_⟩
      obtain ⟨r1, hr1, κ1, hκ1, e1⟩ :=
        cosetOne hX l.pr h.ch_ok h.sel_ok (h.sharp a) hoka i (by omega) β ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2
      obtain ⟨r0, hr0, κ0, hκ0, e0⟩ :=
        cosetOne hX l.pr h.ch_ok h.sel_ok (h.sharp I.mu0) hok0 i (by omega) β0 ⟨w.1, Finset.mem_union_left _ w.2⟩ w.2
      refine ⟨r1 * r0⁻¹, κ0⁻¹ * κ1, mul_mem hr1 (inv_mem hr0), mul_mem (inv_mem hκ0) hκ1, ?_, fun e => absurd e (by omega)⟩
      rw [e1, e0]
      group
  obtain ⟨β0, hw⟩ := key
  choose r κ hr hκ he hr1 using hw
  have gc := fun w => GlobalTheory.T.doubleCoset_reps_conjugate_level_groups I.Ch I.sel (I.tup a) (I.tup I.mu0) (I.cst a) (I.cst I.mu0) (I.idx a) (I.idx I.mu0) I.glob m2
    hX l.pr h.ch_ok (h.sharp a) (h.sharp I.mu0) hoka hok0 i (by omega) β β0 w (r w) (κ w) (hr w) (hκ w) (he w)
  choose x hx1 hxH hxL using gc
  refine ⟨⟨some β0, by simp [hi]⟩, x, fun e w => hx1 w (hr1 w e), ?_⟩
  exact pi_conj ((I.idx a).levG i β) ((I.idx I.mu0).levG i β0) x hxH hxL

end GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjReferenceChartIndexStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_referenceChartIndex : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ b : Idx I.sel (I.tup a) (I.idx a) i, ∃ (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i)
      (x : ∀ w : (B.primes X).vGs, GL (Fin (B.R.N i)) (𝓞 B.fields.E ⧸ w.1.asIdeal)),
      (i + 1 = B.R.m → ∀ w, x w = 1) ∧
      (∀ g : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs), g ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp ↔
        (fun w => x w * g w * (x w)⁻¹) ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp) ∧
      ∀ (g : ↥(levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).grp) (g0 : ↥(levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp),
        (∀ w, g0.1 w = x w * g.1 w * (x w)⁻¹) →
        (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i b).chr g = (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).chr g0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch.idx_match | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch.idx_match | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.IdxMatch.idx_match <;> assumption)
end
