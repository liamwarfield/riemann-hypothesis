module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ClosedPhiOfClosedTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoreUHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasis
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FixOfHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TraceEqNextCoeff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.PowTrHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrStep
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem core {Z R B : Type} [CommRing Z] [CommRing R] [CommRing B] (f : R →+* B) (zc : Z →+* R) (zb : Z →+* B)
    (hz : ∀ x, f (zc x) = zb x) (n a s g : R) (nZ : Z) (hn : zc nZ = n) {d d' : ℕ}
    (V : Matrix (Fin d) (Fin d) R) (V' : Matrix (Fin d') (Fin d') R) (Pm : Matrix (Fin d) (Fin d') Z)
    (e : Fin d → Z) (e' : Fin d' → Z) (h3 : ∀ i j, n ∣ (V * Pm.map zc - Pm.map zc * V') i j)
    (h4 : ∀ i, nZ ∣ (Pm *ᵥ e' - e) i) (ui : Fin d → B) (vj : Fin d' → B) (w : B) (ai : Fin d → R) (bj : Fin d' → R)
    (ha : ∀ i, f (ai i) = f a * ui i) (hv : ∀ j, vj j = f n * f (bj j)) (hw : w = f n * f g) :
    ∃ Y : R, f a * (∑ i, (((V.map f * Pm.map zb - Pm.map zb * V'.map f) *ᵥ (fun j => zb (e' j))) -
        V.map f *ᵥ fun i => zb ((Pm *ᵥ e' - e) i)) i * ui i +
      ∑ j, (V'.map f *ᵥ fun i => zb (e' i)) j * vj j - f s * w) = f (n * Y) := by
  choose W hW using h3
  choose r hr using h4
  have hPb : Pm.map zb = (Pm.map zc).map f := by
    ext i j; simp [hz]
  have hE : (fun j => zb (e' j)) = f ∘ (fun j => zc (e' j)) := by
    ext j; simp [hz]
  have hD : V * Pm.map zc - Pm.map zc * V' = n • Matrix.of W := by
    ext i j; simp [hW]
  have hM : V.map f * Pm.map zb - Pm.map zb * V'.map f = (n • Matrix.of W).map f := by
    rw [← hD, hPb, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul]
  have hq : (fun i => zb ((Pm *ᵥ e' - e) i)) = f ∘ (fun i => n * zc (r i)) := by
    ext i; simp only [Function.comp, hr i, map_mul, hz, ← hn]
  have h1 : ∀ i, (((V.map f * Pm.map zb - Pm.map zb * V'.map f) *ᵥ (fun j => zb (e' j))) -
        V.map f *ᵥ fun i => zb ((Pm *ᵥ e' - e) i)) i =
      f n * f ((Matrix.of W *ᵥ fun j => zc (e' j)) i - (V *ᵥ fun i => zc (r i)) i) := by
    intro i
    rw [hM, hE, hq, Pi.sub_apply, ← RingHom.map_mulVec, ← RingHom.map_mulVec, ← map_mul, ← map_sub]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum, mul_sub]
    congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∀ j, (V'.map f *ᵥ fun i => zb (e' i)) j = f ((V' *ᵥ fun i => zc (e' i)) j) := by
    intro j; rw [hE, ← RingHom.map_mulVec]
  refine ⟨∑ i, ((Matrix.of W *ᵥ fun j => zc (e' j)) i - (V *ᵥ fun i => zc (r i)) i) * ai i +
    ∑ j, a * (V' *ᵥ fun i => zc (e' i)) j * bj j - a * s * g, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h1, h2, hv, hw, map_mul, map_add (f := _), map_sub, map_sum, ha, Finset.mul_sum, mul_add, mul_sub]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

variable {l : ℕ} [Fact l.Prime]

private theorem u_alg {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l]) :
    uB T (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z := by
  show T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l]))) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact T.zB z

private theorem iB_zC (z : ℤ_[l]) : iB l (zC l z) = Per.zB l z := rfl

private theorem exists_iB {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (c : ↥(MaximalUnramifiedExtension l))
    (hc : ‖(c : Om l)‖ ≤ 1) : ∃ y : Per.Acris l, iB l y = uB T c := by
  obtain ⟨w, hw⟩ := GlobalTheory.ExpImage.exists_lifts_of_norm_le_one l P AI T (adjExt (c : Om l)) ⟨c, mem_adjExt _, c.2⟩ hc
  refine ⟨iA l w, ?_⟩
  have h : AI.ιA w = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c := hw
  show _ = T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c)
  rw [← h, T.ιA]
  rfl

private theorem norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  rw [← h]
  congr 1

private theorem scale {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (lam : Om l →ₗ[↥(MaximalUnramifiedExtension l)] ↥(MaximalUnramifiedExtension l)) (n : ℕ) (y : Om l) :
    uB T (lam ((n : Om l) * y)) = (n : Per.Bcris l) * uB T (lam y) := by
  rw [← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trStep_holds :
    Func → TrId → TrStep := by
  intro hF hI l _ P AI T s d d' m M c₁ c₂ t t' c pv p θ Pi e e' V V' h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hn : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := norm_l
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl0 : (l : Om l) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact (inv_pos.2 hlpos).ne hn
  have hlK : (l : ↥(MaximalUnramifiedExtension l)) ≠ 0 := by
    intro h0
    apply hl0
    have := congrArg (fun x : ↥(MaximalUnramifiedExtension l) => (x : Om l)) h0
    simpa using this
  have hsmall : ∀ y : Om l, ‖y‖ ≤ ((l : ℝ) ^ M)⁻¹ → ‖y / (l : Om l) ^ M‖ ≤ 1 := by
    intro y hy
    rw [norm_div, norm_pow, hn, inv_pow]
    exact div_le_one_of_le₀ (by simpa using hy) (by positivity) |>.trans le_rfl
  let δ : Fin d' → Om l := fun j => ∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k
  let η : Om l := θ - ∑ k, c k * pv k
  let x : Fin d ⊕ Fin d' ⊕ Unit → Om l := Sum.elim (fun i => (l : Om l) ^ c₁ * t i)
    (Sum.elim (fun j => δ j / (l : Om l) ^ M) (fun _ => η / (l : Om l) ^ M))
  have hx : ∀ i, ‖x i‖ ≤ 1 := by
    rintro (i | j | _)
    · exact h7 i
    · exact hsmall _ (h5 j)
    · exact hsmall _ h6
  obtain ⟨lam, hl1, hl2, hl3⟩ := hF l (MaximalUnramifiedExtension l) (Fin d ⊕ Fin d' ⊕ Unit) x ((l : Om l) ^ c₁ * (p - θ)) hx h8
  have hid := hI l (Per.Bcris l) (uB T) (Per.zB l) (u_alg T) (iB l s) d d' m t t' c pv p θ Pi e e'
    (V.map (iB l)) (V'.map (iB l)) h1 h2 lam
  choose ai hai using fun i => exists_iB T (lam (x (Sum.inl i))) (hl1 _)
  choose bj hbj using fun j => exists_iB T (lam (x (Sum.inr (Sum.inl j)))) (hl1 _)
  obtain ⟨g, hg⟩ := exists_iB T (lam (x (Sum.inr (Sum.inr ())))) (hl1 _)
  have hpow : ∀ (k : ℕ) (y : Om l), uB T (lam ((l : Om l) ^ k * y)) = (l : Per.Bcris l) ^ k * uB T (lam y) := by
    intro k y
    have := scale T lam (l ^ k) y
    push_cast at this
    exact this
  have hdiv : ∀ y : Om l, uB T (lam y) = (l : Per.Bcris l) ^ M * uB T (lam (y / (l : Om l) ^ M)) := by
    intro y
    rw [← hpow, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨Y, hY⟩ := core (iB l) (zC l) (Per.zB l) iB_zC ((l : Per.Acris l) ^ M) ((l : Per.Acris l) ^ c₁) s g
    ((l : ℤ_[l]) ^ M) (by simp) V V' Pi e e' h3 h4
    (fun i => uB T (lam (t i))) (fun j => uB T (lam (δ j))) (uB T (lam η)) ai bj
    (fun i => by
      rw [hai i]
      simp only [map_pow, map_natCast]
      exact hpow c₁ (t i))
    (fun j => by
      rw [hbj j]
      simp only [map_pow, map_natCast]
      exact hdiv (δ j))
    (by
      rw [hg]
      simp only [map_pow, map_natCast]
      exact hdiv η)
  rw [← hid] at hY
  set q : ↥(MaximalUnramifiedExtension l) := lam ((l : Om l) ^ c₁ * (p - θ)) with hq
  have huq : uB T q = (l : Per.Bcris l) ^ c₁ * uB T (lam (p - θ)) := hpow c₁ (p - θ)
  have hqn : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(q : Om l)‖ := h9.trans hl2
  have hq0 : q ≠ 0 := by
    intro h0
    have h00 : (0 : ℝ) < ((l : ℝ) ^ c₂)⁻¹ := by positivity
    rw [h0, ZeroMemClass.coe_zero, norm_zero] at hqn
    exact absurd hqn (not_le.2 h00)
  have hq' : ‖(((l : ↥(MaximalUnramifiedExtension l)) ^ c₂ / q : ↥(MaximalUnramifiedExtension l)) : Om l)‖ ≤ 1 := by
    push_cast
    rw [norm_div, norm_pow, hn, inv_pow]
    exact div_le_one_of_le₀ hqn (norm_nonneg _)
  obtain ⟨y', hy'⟩ := exists_iB T _ hq'
  refine ⟨Y * y', GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l ?_⟩
  have hqq : q * ((l : ↥(MaximalUnramifiedExtension l)) ^ c₂ / q) = (l : ↥(MaximalUnramifiedExtension l)) ^ c₂ := mul_div_cancel₀ _ hq0
  have hu : uB T q * iB l y' = (l : Per.Bcris l) ^ c₂ := by
    rw [hy', ← map_mul, hqq, map_pow, map_natCast]
  show iB l _ = iB l _
  rw [← mul_assoc, map_mul (iB l) _ y', ← hY]
  simp only [map_mul, map_pow, map_natCast]
  rw [← hu, huq]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.InvUHolds
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem invU_holds : InvU := by
  intro l _ K bk τ hτ
  have hFφ : ∀ a : Ainf l, WittVector.frobenius a = Per.φA l a := fun a => (GlobalTheory.RingBasics.φA_apply l a).symm
  set f : Ainf l →+* Per.Bcris l := (Per.aB l).comp (Per.φA l) with hf
  set alg : Per.Acris l →+* Per.Bcris l := algebraMap (Per.Acris l) (Per.Bcris l) with halg
  have hif : ∀ a : Ainf l, iB l (fI l a) = f a := fun a => by
    simp only [fI, iB, iA, hFφ, hf, RingHom.comp_apply, GlobalTheory.RingIface.aB_eq_alg]
  have hw : IsUnit (f τ) := by
    obtain ⟨-, e, η, ⟨he1, he2⟩, hτe⟩ := hτ
    have hne : e ≠ 1 := by
      rintro rfl; apply he2; simp
    have hmu : IsUnit (Per.aB l (WittVector.teichmuller l e - 1)) :=
      GlobalTheory.CrisLoc.unit_of_root_aB l e he1 hne
    have : f τ = Per.aB l (η : Ainf l) * Per.aB l (WittVector.teichmuller l e - 1) := by
      simp only [hf, RingHom.comp_apply, ← hFφ, hτe, map_mul]
    rw [this]; exact (η.isUnit.map _).mul hmu
  refine ⟨by rw [hif]; exact hw, ?_⟩
  intro N k d ρ F Y Y' Q Q' hY hYY hQQ hε
  have hgal : ∀ g : ↥(GK K), τ ^ N • ((ρ g).val.map (Per.zA l) * Y.map (Per.σA (g : GQ l))) =
      Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) :=
    (GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d _ F Y Y' hY hYY).2.1
  have e2 : (⇑alg ∘ ⇑(fI l)) = ⇑f := funext hif
  obtain ⟨W, hW⟩ := hw.pow N
  set A := Y.map f with hA
  set B := Q.map alg with hB
  refine ⟨((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B), ⟨?_, ?_⟩, ?_⟩
  ·
    have hB' : B * Q'.map alg = alg ((l : Per.Acris l) ^ (2 * k)) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hB, ← Matrix.map_mul, hQQ, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _)]
    have hA' : A * Y'.map f = f τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hA, ← Matrix.map_mul, hYY, GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_one _ (map_zero _) (map_one _), map_pow]
    have hc : IsUnit (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * alg ((l : Per.Acris l) ^ (2 * k)) * f τ ^ (2 * N)) := by
      refine (W⁻¹.isUnit.mul ?_).mul (hw.pow _)
      have h := (isUnit_l_Bcris l).pow (2 * k)
      simpa [halg, map_pow, map_natCast] using h
    obtain ⟨c, hcv⟩ := hc
    set V := Q'.map alg * Y'.map f
    have hUV : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * V = (c : Per.Bcris l) • (1 : Matrix (Fin d) (Fin d) (Per.Bcris l)) := by
      rw [hcv, smul_mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc B, hB', smul_mul_assoc, Matrix.one_mul,
        mul_smul_comm, hA', smul_smul, smul_smul, mul_assoc]
    have h1 : (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • (A * B)) * (((c⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) • V) = 1 := by
      rw [Matrix.mul_smul, hUV, smul_smul, Units.inv_mul, one_smul]
    exact ⟨⟨_, _, h1, mul_eq_one_comm.mp h1⟩, rfl⟩
  · intro g
    set σ := Per.σB (g : GQ l) with hσ
    have hσaB : ∀ a : Ainf l, σ (Per.aB l a) = Per.aB l (Per.σA (g : GQ l) a) :=
      (ActLaws.act_laws l).2.2.2.2.2.1 (g : GQ l)
    have hσf : ∀ a : Ainf l, σ (f a) = f (Per.σA (g : GQ l) a) := fun a => by
      simp only [hf, RingHom.comp_apply, hσaB, ActLaws.φA_σA]
    have hfz : ∀ z : ℤ_[l], f (Per.zA l z) = Per.zB l z := fun z => by
      simp only [hf, RingHom.comp_apply, GlobalTheory.RingIface.zB_eq_aB_zA, (ActLaws.act_laws l).2.2.2.2.2.2.2.2.1 z]
    have hσalg : ∀ x : Per.Acris l, σ (alg x) = alg (sigA (g : GQ l) x) :=
      (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 (g : GQ l)
    have hG := congrArg (fun M => M.map f) (hgal g)
    simp only [GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_mul, Matrix.map_map, map_pow] at hG
    have e1 : (⇑f ∘ ⇑(Per.zA l)) = ⇑(Per.zB l) := funext hfz
    rw [e1, ← hσf] at hG
    have hE := congrArg (fun M => M.map alg) (hε g)
    simp only [Matrix.map_mul, Matrix.map_map] at hE
    rw [e2] at hE
    have eA : A.map σ = Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) := by
      rw [hA, Matrix.map_map]; congr 1; funext a; exact hσf a
    have eB : B.map σ = Q.map (⇑alg ∘ ⇑(sigA (g : GQ l))) := by
      rw [hB, Matrix.map_map]; congr 1; funext a; exact hσalg a
    rw [GlobalTheory.BcrisInv.map_smul_matrix, Matrix.map_mul, eA, eB]
    have hsW : σ ((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hσW : σ (f τ) ^ N = σ (W : Per.Bcris l) := by rw [hW, map_pow]
    rw [hσW, ← hW] at hG
    have hZ : (ρ g).val.map (Per.zB l) * Y.map (⇑f ∘ ⇑(Per.σA (g : GQ l))) =
        (((W⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) * σ (W : Per.Bcris l)) • (A * (F.ε g).map f) := by
      rw [← smul_smul, ← hG, smul_smul, Units.inv_mul, one_smul]
    rw [mul_smul_comm, ← Matrix.mul_assoc, hZ, smul_mul_assoc, Matrix.mul_assoc, hE, smul_smul, mul_left_comm, hsW,
      mul_one]
  · rw [hif, ← hW, smul_smul, Units.mul_inv, one_smul, hA, hB, Matrix.map_mul, Matrix.map_map]
    have e3 : (⇑(iB l) ∘ ⇑(fI l)) = ⇑f := funext hif
    rw [e3]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.LinkRec
namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem linkRec_holds : LinkRec := by
  intro R _ φ lr π v w N d d' α β Q α₁ β₁ β₁' Q₁ R₁ R₀ h1 h2 h3 h4 h5
  obtain ⟨u, hu_def⟩ : ∃ u : R, u = ((v ^ N * w ^ (2 * N))⁻¹ : Rˣ) := ⟨_, rfl⟩
  set s := (lr * (v : R)) ^ N with hs
  set t := (lr * (w : R)) ^ N with ht
  have hvw : u * ((v : R) ^ N * (w : R) ^ (2 * N)) = 1 := by
    rw [hu_def, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, Units.inv_mul]
  have hu : u * (s * (lr * (w : R)) ^ (2 * N)) = lr ^ (3 * N) := by
    calc u * (s * (lr * (w : R)) ^ (2 * N))
        = (u * ((v : R) ^ N * (w : R) ^ (2 * N))) * lr ^ (3 * N) := by
          rw [hs]
          ring
      _ = lr ^ (3 * N) := by rw [hvw, one_mul]
  refine ⟨(u * t) • α, β₁', ?_⟩
  set D4 := R₁ * α₁ - α * R₁.map φ with hD4def
  set D5 := R₀ * β₁ - β * R₀.map φ with hD5def
  have hD4 : α * R₁.map φ = R₁ * α₁ - D4 := by rw [hD4def, sub_sub_cancel]
  have hD5 : β * R₀.map φ = R₀ * β₁ - D5 := by rw [hD5def, sub_sub_cancel]
  have e1 : t • (α * R₁.map φ * Q₁.map φ) = s • (R₁ * Q₁ * β₁) - t • (D4 * Q₁.map φ) := by
    calc t • (α * R₁.map φ * Q₁.map φ) = t • ((R₁ * α₁ - D4) * Q₁.map φ) := by rw [hD4]
      _ = R₁ * (t • (α₁ * Q₁.map φ)) - t • (D4 * Q₁.map φ) := by
        simp only [Matrix.sub_mul, smul_sub, Matrix.mul_smul, Matrix.mul_assoc]
      _ = R₁ * (s • (Q₁ * β₁)) - t • (D4 * Q₁.map φ) := by rw [h3]
      _ = s • (R₁ * Q₁ * β₁) - t • (D4 * Q₁.map φ) := by
        simp only [Matrix.mul_smul, Matrix.mul_assoc]
  have e2 : t • (α * Q.map φ * R₀.map φ) = s • (Q * R₀ * β₁) - s • (Q * D5) := by
    calc t • (α * Q.map φ * R₀.map φ) = (t • (α * Q.map φ)) * R₀.map φ := by rw [Matrix.smul_mul]
      _ = (s • (Q * β)) * R₀.map φ := by rw [h2]
      _ = s • (Q * (β * R₀.map φ)) := by rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = s • (Q * (R₀ * β₁ - D5)) := by rw [hD5]
      _ = s • (Q * R₀ * β₁) - s • (Q * D5) := by
        simp only [Matrix.mul_sub, smul_sub, Matrix.mul_assoc]
  have hmap : (R₁ * Q₁ - Q * R₀).map φ = R₁.map φ * Q₁.map φ - Q.map φ * R₀.map φ := by
    rw [Matrix.map_sub _ (map_sub φ), Matrix.map_mul, Matrix.map_mul]
  have e3 : (u * t) • α * (R₁.map φ * Q₁.map φ - Q.map φ * R₀.map φ)
      = u • (t • (α * R₁.map φ * Q₁.map φ) - t • (α * Q.map φ * R₀.map φ)) := by
    simp only [Matrix.smul_mul, Matrix.mul_sub, smul_sub, smul_smul, Matrix.mul_assoc]
  have key : lr ^ (3 * N) • (R₁ * Q₁ - Q * R₀) - (u * t) • α * (R₁ * Q₁ - Q * R₀).map φ * β₁'
      = (u * t) • (D4 * (Q₁.map φ * β₁')) - (u * s) • (Q * (D5 * β₁')) := by
    rw [hmap, e3, e1, e2, ← hu]
    simp only [Matrix.sub_mul, Matrix.smul_mul, smul_sub, smul_smul, Matrix.mul_assoc, h1,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_sub]
    module
  intro i j
  rw [key, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    Matrix.mul_apply, Matrix.mul_apply]
  refine dvd_sub (dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_left (h4 i k) _) _)
    (dvd_mul_of_dvd_right (Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right ?_ _) _)
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k' _ => dvd_mul_of_dvd_left (h5 k k') _

end UpperTheory.Gal.ClosedPhiFromClosedTrace
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ColInv
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem actQ_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (g : GQ l)
    (y : Per.Bcris l) : P.actQ g (T.eB.symm y) = T.eB.symm (Per.σB g y) := by
  apply T.eB.injective
  rw [T.actB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem phiB_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (y : Per.Bcris l) : P.φB (T.eB.symm y) = T.eB.symm (Per.φB l y) := by
  apply T.eB.injective
  rw [T.frob, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem smul_symm {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l])
    (y : Per.Bcris l) : (z : ℚ_[l]) • T.eB.symm y = T.eB.symm (Per.zB l z * y) := by
  apply T.eB.injective
  rw [Algebra.smul_def, map_mul, T.zB, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

private theorem smul_Cst {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l])
    (y : Per.Bcris l) : (z : ℚ_[l]) • (Polynomial.C (T.eB.symm y) : Bst P) = Polynomial.C (T.eB.symm (Per.zB l z * y)) := by
  rw [← smul_symm T z y]
  exact Polynomial.smul_C (z : ℚ_[l]) (T.eB.symm y)

private theorem sum_Cst {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {ι : Type}
    (s : Finset ι) (f : ι → Per.Bcris l) :
    ∑ i ∈ s, (Polynomial.C (T.eB.symm (f i)) : Bst P) = Polynomial.C (T.eB.symm (∑ i ∈ s, f i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum T.eB.symm]
  exact (map_sum (Polynomial.C : P.R.B →+* Polynomial P.R.B) _ _).symm

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.colInv_holds :
    ColInv := by
  intro l _ P AI T K L a d ρ R v hv U hU j
  refine ⟨?_, fun n => ?_⟩
  · rw [mem_Dst]
    intro g
    have hinv : ∀ i', ∑ i, Per.zB l ((ρ g).val i' i) * Per.σB (g : GQ l) (U i j) = U i' j := fun i' => by
      have h := congrFun (congrFun (hU.inv g) i') j
      simpa [Matrix.mul_apply, Matrix.map_apply] using h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have step : ∀ i, (stRep P R g) (v i ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (U i j)) : Bst P)) =
        ∑ i', v i' ⊗ₜ[ℚ_[l]] (Polynomial.C (T.eB.symm (Per.zB l ((ρ g).val i' i) * Per.σB (g : GQ l) (U i j))) : Bst P) := fun i => by
      rw [stRep_tmul, actSt_C, actQ_symm T, hv, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [← smul_Cst T, TensorProduct.smul_tmul]
    simp only [step]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [← TensorProduct.tmul_sum, sum_Cst T, hinv]
  · induction n with
    | zero => simp
    | succ n ih =>
      set_option synthInstance.maxHeartbeats 100000 in
        rw [pow_succ', Module.End.mul_apply, ih, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [phiV_tmul, phiSt_C, phiB_symm T, pow_succ', RingHom.mul_def, RingHom.comp_apply]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.DvdMulEntriesRight
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem map_smul_ringHom {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) {d : ℕ} (c : S)
    (M : Matrix (Fin d) (Fin d) S) : (c • M).map f = f c • M.map f := by
  ext i j; simp

private theorem dvd_mul_entries_left {T : Type} [CommRing T] {a b e : ℕ} (c : T) (A : Matrix (Fin a) (Fin b) T)
    (B : Matrix (Fin b) (Fin e) T) (h : ∀ i j, c ∣ B i j) (i : Fin a) (j : Fin e) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (h k j) _

private theorem dvd_mul_entries_right {T : Type} [CommRing T] {a b e : ℕ} (c : T) (A : Matrix (Fin a) (Fin b) T)
    (B : Matrix (Fin b) (Fin e) T) (h : ∀ i j, c ∣ A i j) (i : Fin a) (j : Fin e) : c ∣ (A * B) i j := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_right (h i k) _

private theorem map_intertwine {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (ψ : S →+* S) (φ : T →+* T)
    (hf : ∀ s, φ (f s) = f (ψ s)) {d d' : ℕ} (c : S) (A : Matrix (Fin d) (Fin d) S) (A₁ : Matrix (Fin d') (Fin d') S)
    (R : Matrix (Fin d) (Fin d') S) (h : ∀ i j, c ∣ (R * A₁ - A * R.map ψ) i j) (i : Fin d) (j : Fin d') :
    f c ∣ (R.map f * A₁.map f - A.map f * (R.map f).map φ) i j := by
  have e : R.map f * A₁.map f - A.map f * (R.map f).map φ = (R * A₁ - A * R.map ψ).map f := by
    have e' : (R.map f).map φ = (R.map ψ).map f := by
      ext i j; simp [hf]
    rw [e']
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mul_apply, map_sum]
  rw [e, Matrix.map_apply]
  exact map_dvd f (h i j)

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.linkQ_holds :
    ZeroAp → LinkRec → LinkQ := by
  intro hZ hR l _ K bk N M
  obtain ⟨n, hn⟩ := hZ l K bk (3 * N) M
  refine ⟨n, ?_⟩
  intro k d d' A A₁ A₁' Q Q' Q₁ Q₁' R hA hS hS₁ hRel
  obtain ⟨-, -, ⟨v, hv⟩, hφι, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hv' : fA bk bk.E = (l : Per.Acris l) * v := hv
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : (Per.Acris l)ˣ, f0 bk bk.E = (l : Per.Acris l) * w₀ := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
      rw [← hw]; simp
    refine ⟨(Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map (fA bk).toMonoidHom, ?_⟩
    simp [f0, hc]
  have hφA : ∀ s, phiA l (fA bk s) = fA bk (frobS l bk.a s) := fun s => by
    simp only [fA, RingHom.comp_apply, hφι, bk.ev_frob]
  have hφ0 : ∀ s, phiA l (f0 bk s) = f0 bk (frobS l bk.a s) := fun s => by
    rw [show f0 bk s = fA bk (PowerSeries.C (PowerSeries.constantCoeff s)) from rfl, hφA, frobS_C,
      show f0 bk (frobS l bk.a s) = fA bk (PowerSeries.C (PowerSeries.constantCoeff (frobS l bk.a s))) from rfl,
      constantCoeff_frobS_apply]
  have hdiff : ∀ s, uC bk ∣ fA bk s - f0 bk s := fun s => by
    obtain ⟨t, ht⟩ := (PowerSeries.X_dvd_iff (φ := s - PowerSeries.C (PowerSeries.constantCoeff s))).2 (by simp)
    have e : fA bk s - f0 bk s = uC bk ^ l * fA bk t := by
      rw [show f0 bk s = fA bk (PowerSeries.C (PowerSeries.constantCoeff s)) from rfl, ← map_sub, ht, map_mul]
      congr 1
      simp [fA, uC, frobS_X]
    rw [e]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (Fact.out : l.Prime).ne_zero) _
  have hlc : ∀ f : bk.S →+* Per.Acris l, f ((l : bk.S) ^ n) = (l : Per.Acris l) ^ n := fun f => by
    rw [map_pow, map_natCast]
  have h1 : A₁.map (f0 bk) * A₁'.map (f0 bk) =
      ((l : Per.Acris l) * w₀) ^ (2 * N) • (1 : Matrix (Fin d') (Fin d') (Per.Acris l)) := by
    rw [← hw₀, ← Matrix.map_mul, hA, _root_.map_smul_ringHom, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : ((l : Per.Acris l) * v) ^ N • (Q * A.map (f0 bk)) =
      ((l : Per.Acris l) * w₀) ^ N • (A.map (fA bk) * Q.map (phiA l)) := by
    rw [← hv', ← hw₀]; exact hS.frob
  have h3 : ((l : Per.Acris l) * v) ^ N • (Q₁ * A₁.map (f0 bk)) =
      ((l : Per.Acris l) * w₀) ^ N • (A₁.map (fA bk) * Q₁.map (phiA l)) := by
    rw [← hv', ← hw₀]; exact hS₁.frob
  have h4 : ∀ i j, (l : Per.Acris l) ^ n ∣
      (R.map (fA bk) * A₁.map (fA bk) - A.map (fA bk) * (R.map (fA bk)).map (phiA l)) i j := fun i j => by
    rw [← hlc (fA bk)]
    exact map_intertwine (fA bk) (frobS l bk.a) (phiA l) hφA _ A A₁ R hRel i j
  have h5 : ∀ i j, (l : Per.Acris l) ^ n ∣
      (R.map (f0 bk) * A₁.map (f0 bk) - A.map (f0 bk) * (R.map (f0 bk)).map (phiA l)) i j := fun i j => by
    rw [← hlc (f0 bk)]
    exact map_intertwine (f0 bk) (frobS l bk.a) (phiA l) hφ0 _ A A₁ R hRel i j
  obtain ⟨F, F', hF⟩ := hR (Per.Acris l) (phiA l) (l : Per.Acris l) ((l : Per.Acris l) ^ n) v w₀ N d d'
    (A.map (fA bk)) (A.map (f0 bk)) Q (A₁.map (fA bk)) (A₁.map (f0 bk)) (A₁'.map (f0 bk)) Q₁
    (R.map (fA bk)) (R.map (f0 bk)) h1 h2 h3 h4 h5
  refine hn d d' _ F F' ?_ hF
  intro i j
  have hD : R.map (fA bk) * Q₁ - Q * R.map (f0 bk) =
      R.map (fA bk) * (Q₁ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d') (Fin d') (Per.Acris l))) +
        (l : Per.Acris l) ^ k • (R.map (fA bk) - R.map (f0 bk)) -
        (Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) * R.map (f0 bk) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_sub]
    abel
  rw [hD, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply]
  refine dvd_sub (dvd_add (dvd_mul_entries_left _ _ _ hS₁.mod i j) ?_) (dvd_mul_entries_right _ _ _ hS.mod i j)
  rw [smul_eq_mul]
  exact Dvd.dvd.mul_left (hdiff _) _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.CoverJ
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix GlobalTheory.TraceConjugationCover
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem coverJ_holds : CoverJ := by
  intro l _ Γ _ _ _ _ a L₀ r hr hss Cl hCl p θ hap
  classical
  obtain ⟨d, ρ, b, e, hρ, hreads, hind, hbr⟩ := GlobalTheory.T.exists_padicInt_span_image_lattice_regular l Γ a r hr
  obtain ⟨c, hc⟩ := GlobalTheory.T.small_traces_dvd_span_image l Γ a r hr hss
  obtain ⟨K, hK⟩ := traceL l a d b
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hch : ∀ ρ' : Γ →* GL (Fin a) (Om l), ∃ (L : FinExt l) (t : Finset (Matrix (Fin a) (Fin a) (Om l))), Continuous ρ' →
      (L₀.1 ≤ L.1 ∧ (∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) ∧ (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧
        (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧
        (∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c' y) • y = 1) ∧
        ∀ g, ∀ x ∈ t, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t, zOm l (c' y) • y) := by
    intro ρ'
    by_cases h : Continuous ρ'
    · obtain ⟨L, hLf, hL⟩ := GlobalTheory.T.exists_finiteExtension_entries_of_compact_rep l Γ a ρ' h
      haveI := hLf
      haveI := L₀.2
      let L' : FinExt l := ⟨L ⊔ L₀.1, inferInstance⟩
      have hL' : ∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L'.1 := fun g i j =>
        (le_sup_left : L ≤ L ⊔ L₀.1) (hL g i j)
      obtain ⟨t, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_stable_spanning_finset_matrices l Γ a ρ' L' h hL'
      exact ⟨L', t, fun _ => ⟨le_sup_right, hL', h1, h2, h3, h4⟩⟩
    · exact ⟨L₀, ∅, fun h' => absurd h' h⟩
  choose Lf tf htf using hch

  have hap' : ∀ n : ℕ, ∃ (s : Finset (Γ →* GL (Fin a) (Om l))) (cc : (Γ →* GL (Fin a) (Om l)) → Om l),
      (s : Set (Γ →* GL (Fin a) (Om l))) ⊆ Cl ∧ (∀ g, ‖trc r g - ∑ ρ' ∈ s, cc ρ' * trc ρ' g‖ ≤ ((l : ℝ)⁻¹) ^ (n + K + c)) ∧
        ‖θ - ∑ ρ' ∈ s, cc ρ' * p ρ'‖ ≤ ((l : ℝ)⁻¹) ^ (n + K + c) :=
    fun n => hap _ (by positivity)
  choose s cc hsCl hscc hth using hap'
  let U : ℕ → Finset (Γ →* GL (Fin a) (Om l)) := fun n => (Finset.range (n + 1)).biUnion s
  have hUmono : ∀ n, U n ⊆ U (n + 1) := fun n =>
    Finset.biUnion_subset_biUnion_of_subset_left _ (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
  have hsU : ∀ n, s n ⊆ U n := fun n => Finset.subset_biUnion_of_mem s (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hUCl : ∀ n, ∀ ρ' ∈ U n, ρ' ∈ Cl := by
    intro n ρ' h
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
    exact hsCl j hj
  let m : ℕ → ℕ := fun n => (U n).card
  let ρs : ∀ n, Fin (m n) → (Γ →* GL (Fin a) (Om l)) := fun n k => ((U n).equivFin.symm k).1
  have hρsU : ∀ n k, ρs n k ∈ U n := fun n k => ((U n).equivFin.symm k).2
  have hρsC : ∀ n k, Continuous (ρs n k) := fun n k => hCl _ (hUCl n _ (hρsU n k))
  let cs : ∀ n, Fin (m n) → Om l := fun n k => if ρs n k ∈ s n then cc n (ρs n k) else 0
  have hcs : ∀ n (q : (Γ →* GL (Fin a) (Om l)) → Om l), ∑ k, cs n k * q (ρs n k) = ∑ ρ' ∈ s n, cc n ρ' * q ρ' := by
    intro n q
    have e1 : ∑ k, cs n k * q (ρs n k) = ∑ x : (U n), (if x.1 ∈ s n then cc n x.1 else 0) * q x.1 :=
      Fintype.sum_equiv (U n).equivFin.symm _ _ (fun k => rfl)
    rw [e1, Finset.sum_coe_sort (U n) (fun x => (if x ∈ s n then cc n x else 0) * q x)]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsU n)]
  have hK' : ∀ n, ∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ (n + K) • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n w
    rw [Matrix.trace_smul, smul_eq_mul, norm_mul, norm_pow, norm_l]
    calc ((l : ℝ)⁻¹) ^ (n + K) * ‖(∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + K) * (l : ℝ) ^ K :=
          mul_le_mul_of_nonneg_left (hK w) (by positivity)
      _ = ((l : ℝ) ^ n)⁻¹ := by
          rw [pow_add, inv_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  have hlay : ∀ n, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin (m n) → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (Lf (ρs n k)).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin (m n) → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (Lf (ρs n k)).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs n k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ latT (ρs n) (fun k => tf (ρs n k)) M) ∧ (∀ x ∈ latT (ρs n) (fun k => tf (ρs n k)) M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ Carries r b (ρs n) (fun k => tf (ρs n k)) M bb P (n + K) ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs n k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n
    exact GlobalTheory.T.exists_lattice_layer_cover_basis_mod_pow l Γ a r d ρ b e hreads hind hbr c hc n (n + K) (by omega) (hK' n) (m n) (ρs n)
      (fun k => Lf (ρs n k)) (fun k => tf (ρs n k)) (hρsC n) (fun k => (htf _ (hρsC n k)).2.1)
      (fun k => (htf _ (hρsC n k)).2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.1)
      (fun k => (htf _ (hρsC n k)).2.2.2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.2.2) (cs n)
      (fun g => by rw [hcs n (fun ρ' => trc ρ' g)]; exact hscc n g)
  choose M₀ hM₀ using hlay
  let M : ℕ → ℕ := fun n => ∑ j ∈ Finset.range (n + 1), M₀ j
  have hMle : ∀ n, M₀ n ≤ M n := fun n =>
    Finset.single_le_sum (f := M₀) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hMmono : ∀ n, M n ≤ M (n + 1) := fun n => by
    simp only [M]
    rw [Finset.sum_range_succ _ (n + 1)]
    exact Nat.le_add_right _ _
  have hL := fun n => hM₀ n (M n) (hMle n)
  choose d' ρ' bb e' P hcont hbbL hind' hspan' hreads' hmem hcoord hcar honto hunit htr using hL
  let ι : ∀ n, Fin (m n) → Fin (m (n + 1)) := fun n k =>
    (U (n + 1)).equivFin ⟨((U n).equivFin.symm k).1, hUmono n ((U n).equivFin.symm k).2⟩
  have hι : ∀ n k, ρs (n + 1) (ι n k) = ρs n k := by
    intro n k
    simp [ρs, ι]
  have htrans : ∀ n, ∃ f : Matrix (Fin (d' n)) (Fin (d' (n + 1))) ℤ_[l], (∀ g, f * ((ρ' (n + 1) g : GL (Fin (d' (n + 1))) ℤ_[l]) : Matrix (Fin (d' (n + 1))) (Fin (d' (n + 1))) ℤ_[l]) = ((ρ' n g : GL (Fin (d' n)) ℤ_[l]) : Matrix (Fin (d' n)) (Fin (d' n)) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P n * f - P (n + 1)) i j := by
    intro n
    exact GlobalTheory.T.exists_equivariant_transition_matrix_cover l Γ a r d b hind (m n) (m (n + 1)) (ρs n) (ρs (n + 1)) (ι n) (hι n)
      (fun k => tf (ρs n k)) (fun k => tf (ρs (n + 1) k)) (fun k => by rw [hι n k]) (M n) (M (n + 1)) (hMmono n)
      (d' n) (d' (n + 1)) (ρ' n) (ρ' (n + 1)) (bb n) (bb (n + 1)) (e' n) (e' (n + 1)) (hind' n) (hreads' n)
      (hreads' (n + 1)) (hmem (n + 1)) (hcoord n) (P n) (P (n + 1)) n (n + K) (n + 1 + K) (by omega) (by omega)
      (hcar n) (hcar (n + 1))
  choose f hfe hfP using htrans
  let tw : Tower ρ :=
    { d' := d', ρ' := ρ', Pi := P, onto := honto, f := f, f_equi := hfe, f_Pi := hfP }
  let lay : ∀ n, Layer L₀ Cl (tw.ρ' n) := fun n =>
    { m := m n, rep := ρs n, mem := fun k => hUCl n _ (hρsU n k), L := fun k => Lf (ρs n k),
      le := fun k => (htf _ (hρsC n k)).1, rep_mem := fun k => (htf _ (hρsC n k)).2.1, b := bb n,
      b_mem := hbbL n, indep := hind' n, span := hspan' n, e := e' n, reads := hreads' n, c := cs n }
  refine ⟨{ d := d, ρ := ρ, cont := hρ, b := b, e := e, reads := hreads, tw := tw, cont' := hcont, lay := lay,
            unit := hunit, trace := htr }, fun n => ?_⟩
  show ‖θ - ∑ k, cs n k * p (ρs n k)‖ ≤ _
  rw [hcs n p]
  refine (hth n).trans ?_
  rw [← inv_pow]
  exact pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hl1.le) (by omega)

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.SecUHolds
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem secU_holds : CoreU → SecU := by
  intro hU l _ K bk N
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.AcrisPow.main l K bk (2 * N + 1) 1
  refine ⟨n₀ + 2 * N * n₀, fun d A A' hA => ?_⟩
  set ψ : bk.S →+* Per.Acris l := (algebraMap (Ainf l) (Per.Acris l)).comp bk.ev with hψ
  obtain ⟨htor, hcomp, ⟨v, hv⟩, hφ, -⟩ := GlobalTheory.AcrisFrobE.main l K bk
  have hφψ : ∀ s, phiA l (ψ s) = ψ (frobS l bk.a s) := fun s => by
    simp only [hψ, RingHom.comp_apply, hφ, bk.ev_frob]
  have hu : phiA l (ψ X) = ψ X ^ l := by rw [hφψ, frobS_X, map_pow]
  have hdiff : ∀ s : bk.S, ∃ t : Per.Acris l,
      ψ (frobS l bk.a s) - ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff s))) = ψ X ^ l * t := by
    intro s
    obtain ⟨t, ht⟩ := (PowerSeries.X_dvd_iff (φ := s - PowerSeries.C (PowerSeries.constantCoeff s))).2 (by simp)
    refine ⟨ψ (frobS l bk.a t), ?_⟩
    rw [← map_sub, ← map_sub, ht, map_mul, frobS_X, map_mul, map_pow]
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hE0 : PowerSeries.constantCoeff bk.E = bk.Ep.coeff 0 := by simp
  set w0 : Per.Acris l := ψ (frobS l bk.a (PowerSeries.C (w : Wq l bk.a))) with hw0def
  have hw0u : IsUnit w0 := ((w.isUnit.map PowerSeries.C).map (frobS l bk.a)).map ψ
  have hP0 : ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) = (l : Per.Acris l) * w0 := by
    rw [hE0, hw, map_mul, map_natCast, map_mul, map_natCast, map_mul, map_natCast]
  set u : Per.Acris l := ψ X with hudef
  set P : Per.Acris l := ψ (frobS l bk.a bk.E) with hPdef
  set a : Per.Acris l := ((v⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hadef
  set b : Per.Acris l := ((hw0u.unit⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) with hbdef
  have hav : a * v = 1 := Units.inv_mul v
  have hbw : b * w0 = 1 := by rw [hbdef]; exact hw0u.val_inv_mul
  set fB : bk.S →+* Per.Acris l := ψ.comp (frobS l bk.a) with hfB
  set fB0 : bk.S →+* Per.Acris l := fB.comp (PowerSeries.C.comp PowerSeries.constantCoeff) with hfB0
  have hmap : ∀ f : bk.S →+* Per.Acris l, (A.map f) * (A'.map f) = (f bk.E) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
    intro f
    rw [← Matrix.map_mul, hA]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hfE : fB bk.E = (l : Per.Acris l) * v := hv
  have hfE0 : fB0 bk.E = (l : Per.Acris l) * w0 := hP0
  have hcoef : ∀ (c y : Per.Acris l), c * y = 1 → c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N) := by
    intro c y h
    calc c ^ N * c ^ N * ((l : Per.Acris l) * y) ^ (2 * N) = (l : Per.Acris l) ^ (2 * N) * (c * y) ^ (2 * N) := by ring
      _ = _ := by rw [h, one_pow, mul_one]
  have hα : (a ^ N • A.map fB) * (a ^ N • A'.map fB) = ((l : Per.Acris l) ^ (2 * N)) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hmap, hfE, smul_smul, smul_smul, hcoef a v hav]
  have hβ : (b ^ N • A.map fB0) * (b ^ N • A'.map fB0) = ((l : Per.Acris l) ^ (2 * N)) • 1 := by
    rw [smul_mul_assoc, mul_smul_comm, hmap, hfE0, smul_smul, smul_smul, hcoef b w0 hbw]
  choose G hG using fun i j => hdiff (A i j)
  obtain ⟨z, hz⟩ := hdiff bk.E
  obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow w0 v N
  have hΓ : (l : Per.Acris l) • (a ^ N • A.map fB - b ^ N • A.map fB0) =
      u ^ l • ((((l : Per.Acris l) * a ^ N) • Matrix.of G) + (-(a ^ N * b ^ N * z * t)) • A.map fB0) := by
    ext i j
    have h1 : fB (A i j) - fB0 (A i j) = u ^ l * G i j := hG i j
    have h2 : (l : Per.Acris l) * v - (l : Per.Acris l) * w0 = u ^ l * z := by rw [← hfE, ← hfE0]; exact hz
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
      smul_eq_mul]
    have h4 : (a * v) ^ N = 1 := by rw [hav, one_pow]
    have h5 : (b * w0) ^ N = 1 := by rw [hbw, one_pow]
    linear_combination ((l : Per.Acris l) * a ^ N) * h1 + (-(a ^ N * b ^ N * t * fB0 (A i j))) * h2 +
      ((l : Per.Acris l) * a ^ N * b ^ N * fB0 (A i j)) * ht + ((l : Per.Acris l) * fB0 (A i j) * b ^ N) * h4 +
      (-((l : Per.Acris l) * fB0 (A i j) * a ^ N)) * h5
  obtain ⟨Q, Q', hQQ, ⟨Y, hY⟩, ⟨Y', hY'⟩, hQ⟩ := hU (Per.Acris l) d l l N htor hcomp (phiA l) u hu
    (Fact.out : l.Prime).pos _ _ _ _ _ hα hβ hΓ n₀ (fun n hn => hn₀ (n + 1) (by omega))
  refine ⟨Q, Q', ⟨hQQ, fun i j => ⟨Y i j, ?_⟩, fun i j => ⟨Y' i j, ?_⟩, ?_⟩⟩
  · rw [hY]; rfl
  · rw [hY']; rfl
  · have key : b ^ N • (Q * A.map fB0) = a ^ N • (A.map fB * Q.map (phiA l)) := by
      rw [← mul_smul_comm, hQ, smul_mul_assoc]
    have e1 : P ^ N = (P ^ N * w0 ^ N) * b ^ N := by
      rw [mul_assoc, ← mul_pow, mul_comm w0 b, hbw, one_pow, mul_one]
    have e2 : (P ^ N * w0 ^ N) * a ^ N = ((l : Per.Acris l) * w0) ^ N := by
      rw [hv]
      calc ((l : Per.Acris l) * v) ^ N * w0 ^ N * a ^ N = ((l : Per.Acris l) * w0) ^ N * (a * v) ^ N := by ring
        _ = _ := by rw [hav, one_pow, mul_one]
    show P ^ N • (Q * A.map fB0) =
      ψ (frobS l bk.a (PowerSeries.C (PowerSeries.constantCoeff bk.E))) ^ N • (A.map fB * Q.map (phiA l))
    rw [hP0, e1, ← smul_smul, key, smul_smul, e2]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ZeroAp
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.zeroAp_holds :
    ZeroAp := by
  intro l _ K bk c M
  obtain ⟨htor, -, -, hphi, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually l K bk c M
  refine ⟨c * n₀ + M, ?_⟩
  intro d d' D F F' hdiv hcong
  have hdiv' : ∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D i j := hdiv
  set u := ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X with hu
  have hφu : phiA l u = u ^ l := by
    rw [hu, RingHom.comp_apply, hphi, ← bk.ev_frob]
    have : frobS l bk.a X = X ^ l := by simp [frobS]
    rw [this, map_pow, map_pow]
  have hφl : ∀ k : ℕ, phiA l ((l : Per.Acris l) ^ k) = (l : Per.Acris l) ^ k := by
    intro k; simp
  set P : Per.Acris l := (l : Per.Acris l) ^ (c * n₀ + M) with hP
  have hφP : phiA l P = P := hφl _
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin d) (Fin d') (Per.Acris l),
      (l : Per.Acris l) ^ c • D = F * D.map (phiA l) * F' + P • G := by
    refine ⟨Matrix.of fun i j => (hcong i j).choose, ?_⟩
    ext i j
    have h := (hcong i j).choose_spec
    rw [Matrix.add_apply, Matrix.smul_apply (P), Matrix.of_apply, smul_eq_mul, ← h,
      Matrix.sub_apply]
    ring
  have key : ∀ t : ℕ, ∃ N H : Matrix (Fin d) (Fin d') (Per.Acris l),
      (l : Per.Acris l) ^ (c * t) • D = u ^ (l ^ t) • N + P • H := by
    intro t
    induction t with
    | zero =>
      refine ⟨Matrix.of fun i j => (hdiv' i j).choose, 0, ?_⟩
      ext i j
      simp only [mul_zero, pow_zero, pow_one, one_smul, smul_zero, add_zero, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul]
      rw [one_mul]
      exact (hdiv' i j).choose_spec
    | succ t ih =>
      obtain ⟨N, H, hNH⟩ := ih
      refine ⟨F * N.map (phiA l) * F', F * H.map (phiA l) * F' + (l : Per.Acris l) ^ (c * t) • G, ?_⟩
      have hmap : ((l : Per.Acris l) ^ (c * t) • D).map (phiA l)
          = (l : Per.Acris l) ^ (c * t) • D.map (phiA l) := by
        ext i j; simp [hφl]
      have hmap2 : (u ^ (l ^ t) • N + P • H).map (phiA l)
          = u ^ (l ^ (t + 1)) • N.map (phiA l) + P • H.map (phiA l) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
          map_mul, map_pow, hφu, hφP]
        rw [← pow_mul, pow_succ' l t]
      calc (l : Per.Acris l) ^ (c * (t + 1)) • D
          = (l : Per.Acris l) ^ (c * t) • ((l : Per.Acris l) ^ c • D) := by
            rw [smul_smul, ← pow_add, mul_add, mul_one]
        _ = F * (((l : Per.Acris l) ^ (c * t) • D).map (phiA l)) * F'
              + P • ((l : Per.Acris l) ^ (c * t) • G) := by
            rw [hG, hmap, smul_add, Matrix.mul_smul, Matrix.smul_mul, smul_comm P]
        _ = u ^ (l ^ (t + 1)) • (F * N.map (phiA l) * F')
              + P • (F * H.map (phiA l) * F' + (l : Per.Acris l) ^ (c * t) • G) := by
            rw [hNH, hmap2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.smul_mul, smul_add, add_assoc]
  intro i j
  obtain ⟨N, H, hNH⟩ := key n₀
  obtain ⟨y, hy⟩ := hn₀ n₀ le_rfl
  have hent : (l : Per.Acris l) ^ (c * n₀) * D i j = u ^ (l ^ n₀) * N i j + P * H i j := by
    have := congrFun (congrFun hNH i) j
    simpa using this
  have hpos : 1 ≤ l ^ n₀ := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hsplit : u ^ (l ^ n₀) = u * u ^ (l ^ n₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨u * y * N i j + H i j, ?_⟩
  apply GlobalTheory.CrZero.pow_cancel _ htor (c * n₀)
  rw [hent, hsplit, hy, hP, pow_add]
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrLinHolds
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLin_holds :
    TrLin := by
  intro k B W J _ _ _ _ _ _ a ha κ ψ hψ T x w h
  classical
  let bW : Module.Basis (Fin a) k W := Module.finBasisOfFinrankEq k W ha
  have hexp : ∀ (y : W) (i : Fin a), ψ y i = ∑ m, κ (bW.repr y m) * ψ (bW m) i := by
    intro y i
    conv_lhs => rw [← bW.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hψ, Pi.smul_apply, smul_eq_mul]
  let X : Matrix (Fin a) (Fin a) B := Matrix.of fun i m => ψ (bW m) i
  let X' : Matrix (Fin a) (Fin a) B := Matrix.of fun m i' => ∑ j, w j * κ (bW.repr (x j i') m)
  have hXX : X * X' = 1 := by
    ext i i'
    rw [Matrix.mul_apply, Matrix.one_apply, ← h i i']
    simp only [X, X', Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hexp (x j i') i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hXX' : X' * X = 1 := mul_eq_one_comm.mp hXX
  let Tm : Matrix (Fin a) (Fin a) B := (LinearMap.toMatrix bW bW T).map κ
  have hrepr : ∀ (y : W) (m : Fin a),
      bW.repr (T y) m = ∑ m', LinearMap.toMatrix bW bW T m m' * bW.repr y m' := by
    intro y m
    rw [← LinearMap.toMatrix_mulVec_repr bW bW T y]
    rfl
  have hentry : ∀ i i', ∑ j, w j * ψ (T (x j i')) i = (X * Tm * X') i i' := by
    intro i i'
    have hTX : ∀ y : W, ψ (T y) i = ∑ m, (X * Tm) i m * κ (bW.repr y m) := by
      intro y
      rw [hexp (T y) i]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hrepr, map_sum, map_mul, Matrix.mul_apply, X, Tm, Matrix.of_apply,
        Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
    rw [Matrix.mul_apply]
    simp only [hTX, X', Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring
  have htr : Matrix.trace Tm = κ (LinearMap.trace k W T) := by
    rw [LinearMap.trace_eq_matrix_trace k bW T]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, Tm, map_sum]
  calc ∑ i, ∑ j, w j * ψ (T (x j i)) i = Matrix.trace (X * Tm * X') := by
        simp only [Matrix.trace, Matrix.diag_apply, hentry]
    _ = Matrix.trace (X' * X * Tm) := by
        rw [Matrix.trace_mul_cycle]
    _ = κ (LinearMap.trace k W T) := by
        rw [hXX', one_mul, htr]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.FuncHolds
noncomputable section

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

open Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Per

theorem func_holds : IntBasis → Func := by
  intro hB l _ F I _ x z hx hz
  classical
  letI : Fintype I := Fintype.ofFinite I
  let eqv := Fintype.equivFin (Option I)
  let y : Fin (Fintype.card (Option I)) → Om l := fun k => (eqv.symm k).elim z x
  have hy : ∀ k, ‖y k‖ ≤ 1 := by
    intro k
    dsimp only [y]
    cases eqv.symm k with
    | none => simpa using hz
    | some i => simpa using hx i
  obtain ⟨m, e, hli, he, hc⟩ := hB l F _ y hy
  choose c hc1 hc2 using hc
  have hyz : y (eqv none) = z := by simp [y]
  have hyx : ∀ i, y (eqv (some i)) = x i := by intro i; simp [y]
  by_cases hz0 : z = 0
  · refine ⟨0, ?_, ?_, ?_⟩ <;> simp [hz0]
  have hm : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    apply hz0
    rw [← hyz, hc2, hne, Finset.sum_empty]
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ
    (fun j => ‖((c (eqv none) j : ↥F) : Om l)‖) hm
  let f : (Fin m → ↥F) →ₗ[↥F] Om l := Fintype.linearCombination ↥F e
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    funext j
    exact Fintype.linearIndependent_iff.1 hli a (by simpa [f, Fintype.linearCombination_apply] using ha) j
  obtain ⟨G, hG⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let lam : Om l →ₗ[↥F] ↥F := LinearMap.proj j₀ ∘ₗ G
  have key : ∀ a : Fin m → ↥F, lam (∑ j, (a j : Om l) * e j) = a j₀ := by
    intro a
    have h1 : (∑ j, (a j : Om l) * e j) = f a := by
      simp only [f, Fintype.linearCombination_apply]
      rfl
    have h2 : G (f a) = a := by
      have := LinearMap.congr_fun hG a
      simpa using this
    rw [h1]
    simp only [lam, LinearMap.comp_apply, h2, LinearMap.proj_apply]
  have hlz : lam z = c (eqv none) j₀ := by
    rw [← hyz, hc2, key]
  refine ⟨lam, ?_, ?_, ?_⟩
  · intro i
    rw [← hyx i, hc2, key]
    exact hc1 _ _
  · rw [hlz]
    rw [← hyz, hc2]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
    intro j _
    rw [norm_mul]
    calc ‖((c (eqv none) j : ↥F) : Om l)‖ * ‖e j‖
        ≤ ‖((c (eqv none) j : ↥F) : Om l)‖ * 1 :=
          mul_le_mul_of_nonneg_left (he j) (norm_nonneg _)
      _ = ‖((c (eqv none) j : ↥F) : Om l)‖ := mul_one _
      _ ≤ _ := hj₀ j (Finset.mem_univ j)
  · rw [hlz]
    exact hc1 _ _

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
end

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem ClosedTr_holds : ClosedTr :=
  closedTr_of coverJ_holds frEx_holds
    (opEx_holds (secU_holds coreU_holds) invQ_holds invU_holds (linkZ_holds linkA_holds (linkQ_holds zeroAp_holds linkRec_holds))
      linkOp_holds fixW_holds opOne_holds)
    fixOf_holds
    (tie_holds (tieRep_holds trLin_holds coordEx_holds coordWD_holds colInv_holds weilPhi_holds testTr_holds))
    (trLim_holds (trStep_holds (func_holds intBasis_holds) trId_holds))

theorem congPhi_holds : GlobalTheory.CongPhi.ClosedPhi := congPhi_of_closedTr ClosedTr_holds powTr_holds

end UpperTheory.Gal.ClosedPhiFromClosedTrace
