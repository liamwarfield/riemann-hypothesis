module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopInvariant
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopXiInv

open Formalism.L2.Col.LocE Formalism.L2.Col.Loc

theorem xiTop_invariant : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 : ℕ) (u : Pr.Word), Pr.Ok → R.m = m2 + 2 → cst.Ok → (∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (p' : TopPt R sel mu u), Y ∈ ybSet sel mu cst p.deco.1.N → ∀ x z, z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) → XiTop Ch sel mu cst m2 p Y p' (x + z) = XiTop Ch sel mu cst m2 p Y p' x := by
  classical
  intro X Pr R Ch sel S mu cst m2 u hPr hm hc hD p Y p' hY x y hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  set c : ℕ := cBof sel mu cst u with hcdef
  change XiTop Ch sel mu cst m2 p Y p' (x + (c : 𝓞 X.E) • y₀) = _
  unfold TopStep.XiTop
  refine congrArg₂ (· * ·) ?_ ?_
  · refine GlobalTheory.TopInv.phiT_add _ _ p'.deco.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
    have h1 : Pr.piT u ∈ P.1.asIdeal := by
      have h := P.2
      unfold Primes.vT divs at h
      split_ifs at h with hf
      · simpa using h
      · simp at h
    rw [hcdef, cBof, Nat.cast_mul, ← hPr.piT_norm]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
  · refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 := GlobalTheory.TopInv.qOf_ne P.1
    rw [GlobalTheory.TopInv.inFr_add]
    generalize inFr (frsF sel mu p P) (frsF sel mu p' P) x = x'
    have hz : ∀ v : Sp X.E (R.N (m2 + 1)), (∀ l, IntAt P.1 (v l)) → ∀ l,
        IntAt P.1 (inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) v l / (qOf P.1 : X.E) ^ cst.B) := by
      intro v hv l
      have h1 : frsF sel mu p P v ∈ p.deco.1.at P.1 := (frsF_mem p P v).2 ((mem_localization_standardLattice _ _).2 hv)
      have h2 := hy₀ P.1 (Finset.mem_union_right _ P.2) _ h1
      have h3 : (frsF sel mu p' P).symm (y₀ (frsF sel mu p P v)) ∈ stdAt X.E _ P.1 := by
        refine (frsF_mem p' P _).1 ?_
        rw [LinearEquiv.apply_symm_apply]
        exact h2
      have h4 := (mem_localization_standardLattice _ _).1 h3 l
      obtain ⟨c', hc'⟩ : qOf P.1 ^ cst.B ∣ c :=
        Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _
      have h5 : inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) v l =
          (c : X.E) * (frsF sel mu p' P).symm (y₀ (frsF sel mu p P v)) l := by
        change (frsF sel mu p' P).symm ((c : 𝓞 X.E) • y₀ (frsF sel mu p P v)) l = _
        rw [equiv_osmul, Nat.cast_smul_eq_nsmul, Pi.smul_apply, nsmul_eq_mul]
      rw [h5, hc']
      convert (GlobalTheory.TopInv.intAt_nat (P := P.1) c').mul h4 using 1
      push_cast
      field_simp
    generalize inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) = z at hz ⊢
    unfold locTop
    rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine GlobalTheory.TopInv.PhiTop_add mu Ch _ _ hm P.1 _ _ fun s l => ?_
      have h1 := hz (LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) (Pi.single s 1)) fun l' =>
        GlobalTheory.TopInv.single_int s _
      have h2 := GlobalTheory.TopInv.intAt_div_pow_le hq0 hc.B_pos (h1 (Br.iC (N_m_succ R) l))
      rw [pow_one] at h2
      exact h2
    · refine GlobalTheory.TopInv.ftY_add sel mu cst hc P (hD P) _ _ _ (fun s => ?_) ?_
      · exact GlobalTheory.TopInv.atNL_int (R.N R.m - 1) _ _ (hz (Pi.single s 1) (GlobalTheory.TopInv.single_int s))
      · have h1 := GlobalTheory.TopInv.repY_mem sel mu cst _ _ hY P
        have h2 := (frsF_mem p P ((frsF sel mu p P).symm
          (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 1 else cst.M)) • repY Y))).1 (by
            rw [LinearEquiv.apply_symm_apply]
            exact h1)
        intro l
        have h3 := (mem_localization_standardLattice _ _).1 h2 l
        rw [map_smul] at h3
        exact h3

end GlobalTheory.TopXiInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopSource
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopSrc

open GlobalTheory.DatumLaw

theorem of_zero {E : Type} [Field E] {n c : ℕ} (hc : c = 0) (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (κ : Sp E n ≃ₗ[E] Sp E n)
    (h : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (κ x)) :
    κ.toLinearMap ∘ₗ LinearMap.funLeft E E (Fin.castAdd c) = LinearMap.funLeft E E (Fin.castAdd c) ∘ₗ r.toLinearMap ∧
      LinearEquiv.det κ = LinearEquiv.det r ∧ Loc.n1Arg r = 0 := by
  subst hc
  have e : ∀ x : Sp E n, Loc.inX E n 0 x = x := fun x => by
    funext l
    rw [CongLevel.inX_apply]
    exact dif_pos l.2
  have hr : r = κ := LinearEquiv.ext fun x => by
    have := h x
    rwa [e, e] at this
  subst hr
  refine ⟨rfl, rfl, ?_⟩
  unfold Loc.n1Arg
  simp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem phiTop_source (sharp : Bool) {m2 : ℕ} (hm : R.m = m2 + 2) (P : rowSG Pr sel mu) {g : AutY X R (m2 + 1)}
    (hg : g ∈ Jat (Pr := Pr) sharp (m2 + 1) P.1) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) :
    PhiTop Ch mu sharp m2 P.1 (x ∘ₗ g.toLinearMap) * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      lamRow Ch mu sharp (m2 + 1) P.1 g.toLinearMap * PhiTop Ch mu sharp m2 P.1 x := by
  obtain ⟨a1, a2, a3, a4⟩ := ranks R (j := m2 + 1) (by omega)
  have b1 := rank_X'_eq R
  have b2 : R.r + (m2 + 1) * R.t ≤ R.N R.m - 1 + 0 := by
    rw [b1, add_zero]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hb : R.r ≤ R.N R.m - 1 + 0 := by omega
  unfold rhoS
  unfold Jat at hg
  unfold PhiTop lamRow
  generalize R.N R.m - 1 = n at *
  have e1 := fun ψ χ => hm ▸ phiGS_eq (K := X.K) (P := P.1) ψ χ (k₀ := R.k) (rS := R.rS) (r := R.r) (t := R.t) (i := m2 + 1)
    (c' := cOf R (m2 + 1)) (n' := R.N (m2 + 1)) (c := 0) (n := n)
  have e2 := fun ψ χ => hm ▸ phiG_eq (K := X.K) (P := P.1) ψ χ (k₀ := R.k) (r := R.r) (t := R.t) (i := m2 + 1)
    (c' := cOf R (m2 + 1)) (n' := R.N (m2 + 1)) (c := 0) (n := n)
  split_ifs at hg ⊢
  · rw [e1]
    exact phiM_source _ _ (by omega) (by omega) a1 b2 _ inf_le_left
      (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x
  · rw [e2, LocE.lamGB, lamGv_eq]
    exact phiM_source _ _ (by omega) (by omega) a1 b2 _ inf_le_left
      (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x
  · exact phiQ_source _ (by omega) a2 a3 hb hg x

theorem phiTop_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu) (κ : GLint X.E (R.N (m2 + 1)) P.1) (c : X.Kˣ), (∀ hP : P.1 ∈ Pr.vGs, ∃ h : redGL _ P.1 κ ∈ (L.levG (m2 + 1) b ⟨P.1, hP⟩).H, c = (L.levG (m2 + 1) b ⟨P.1, hP⟩).lam ⟨_, h⟩) → (∀ hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K), P.1 ∉ Pr.vGs → ∃ h : κ ∈ (L.levQ (m2 + 1) b ⟨P.1, hQ⟩).H, c = (L.levQ (m2 + 1) b ⟨P.1, hQ⟩).lam ⟨κ, h⟩) → ∀ x : HomE X.E (R.N (m2 + 1)) ((R.N R.m - 1) + 0), PhiTop Ch mu cst.sharp m2 P.1 (x ∘ₗ κ.1.toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) = (c : X.K) * PhiTop Ch mu cst.sharp m2 P.1 (x ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hL b P κ c hG hQ x
  have hc : cOf R (m2 + 1) = 0 := by
    have := hL.hm
    unfold cOf
    omega
  have key : ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (m2 + 1) P.1) (L.h (m2 + 1) b P),
      (∀ x, r (Loc.inX X.E _ (cOf R (m2 + 1)) x) = Loc.inX X.E _ (cOf R (m2 + 1)) (κ.1 x)) ∧
        (c : X.K) = chiInv Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) r := by
    by_cases hP : P.1 ∈ Pr.vGs
    · obtain ⟨h, rfl⟩ := hG hP
      obtain ⟨g, hg, hred⟩ := (hL.grpG (m2 + 1) b ⟨P.1, hP⟩ _).1 h
      have hgi : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hL.int (m2 + 1) b P hg
      have e : redGL _ P.1 ⟨g, hgi⟩ = redGL _ P.1 κ := redGL_eq _ hred
      have h1 : redGL _ P.1 ((⟨g, hgi⟩ : GLint X.E (R.N (m2 + 1)) P.1)⁻¹ * κ) = 1 := by
        rw [map_mul, map_inv, e, inv_mul_cancel]
      have h2 := CongLevel.cong_mem_prCat X Pr R cst.sharp (m2 + 1) P.1 hP
        (fun a ha h0 => intAt_div_of_redP (qOf_notMem_sq hX hPr hP) ha h0) _ (hL.stabG (m2 + 1) b P hP)
        _ ((⟨g, hgi⟩ : GLint X.E (R.N (m2 + 1)) P.1)⁻¹ * κ).2 fun x hx => by
          rw [redV_redGL _ hx, h1, Units.val_one, Matrix.one_mulVec]
      have h3 : κ.1 ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) := by
        have := mul_mem hg h2
        rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
      obtain ⟨r, hr, hrx⟩ := h3
      exact ⟨r, hr, hrx, hL.chrG (m2 + 1) b ⟨P.1, hP⟩ ⟨_, h⟩ κ.1 r hr hrx fun x hx => redV_redGL κ hx⟩
    · have hP' := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
      obtain ⟨h, rfl⟩ := hQ hP' hP
      have h3 := h
      rw [hL.grpQ, Subgroup.mem_subgroupOf] at h3
      obtain ⟨r, hr, hrx⟩ := h3
      exact ⟨r, hr, hrx, hL.chrQ (m2 + 1) b ⟨P.1, hP'⟩ ⟨_, h⟩ r hr hrx⟩
  obtain ⟨r, hr, hrx, hcr⟩ := key
  rw [hL.last_h] at hr hcr
  have hJ : r ∈ Jat (Pr := Pr) cst.sharp (m2 + 1) P.1 := by simpa using hr.2
  obtain ⟨e1, e2, e3⟩ := of_zero hc r κ.1 hrx
  unfold chiInv at hcr
  rw [e3, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul, inv_one, one_mul, mul_one] at hcr
  rw [e1, e2, hcr, ← LinearMap.comp_assoc]
  exact phiTop_source Ch sel mu cst.sharp hL.hm P hJ _

end GlobalTheory.TopSrc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetGen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopTargetGen

open GlobalTheory.DatumLaw

section General

theorem coarse_rep {r t m i : ℕ} (ht : 0 < t) (h1 : r ≤ i) (h2 : i < r + m * t) :
    coarse r (List.replicate m t) i = (i - r) / t + 1 := by
  rw [coarse_of_le h1, blkIdx_replicate ht _ _ (by omega)]

theorem supSum_eq {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (M : Matrix (Fin n) (Fin n) κ) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = M i j) :
    supSum r (Finset.range (r - 1)) M = ∑ i ∈ Finset.range (r - 1), A i (i + 1) := by
  unfold supSum
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i.val + 1 = j.val ∧ j.val < r ∧ i.val ∈ Finset.range (r - 1) then M i j else 0) =
      if i.1 < r - 1 then A i.1 (i.1 + 1) else 0 := fun i => by
    split_ifs with h
    · rw [Finset.sum_eq_single (⟨i.1 + 1, by omega⟩ : Fin n), if_pos ⟨rfl, by simp only; omega, Finset.mem_range.2 h⟩, ← hA]
      · intro j _ hj
        exact if_neg fun h' => hj (Fin.ext h'.1.symm)
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · exact Finset.sum_eq_zero fun j _ => if_neg fun h' => h (Finset.mem_range.1 h'.2.2)
  rw [Finset.sum_congr rfl fun i _ => h1 i,
    Fin.sum_univ_eq_sum_range (fun i => if i < r - 1 then A i (i + 1) else 0) n, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem lamJ_eq {κ K : Type} [CommRing κ] [Field K] (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {n r t m : ℕ} (ht : 0 < t)
    (hn : n = r + m * t) (M : HJ κ n r t m) (A : ℕ → ℕ → κ)
    (hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j) :
    ((lamJ ψ χ n r t m M : Kˣ) : K) = lamF ψ χ r r t m A := by
  unfold lamJ lamGen lamF
  rw [MonoidHom.mul_apply, Units.val_mul, supChar_val, supSum_eq (by omega) _ A hA, MonoidHom.comp_apply, detChar_apply,
    List.length_replicate, Units.coe_prod]
  congr 1
  · simp
  refine Finset.prod_congr rfl fun s hs => ?_
  rw [Finset.mem_range] at hs
  have hb : r + s * t + t ≤ n := blk_le hs hn.ge
  rw [← GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t hb ?_
    (Subgroup.inclusion (uniUT_le_blockUT n κ r _) M) A hA]
  · unfold ext0
    rw [dif_pos (Units.isUnit _), IsUnit.unit_of_val_units]
  · intro i hi
    by_cases h : i < r
    · rw [coarse_of_lt h]
      omega
    · rw [coarse_rep ht (by omega) (by omega), Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem red_entB (k₀ : ℕ) {n : ℕ} (ex : ℕ → ℕ) (j : GLint E n P) (p p' : Fin n) :
    redP P (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0)) p.1 p'.1) =
      (redGL n P j : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) p p' := by
  rw [GlobalTheory.TopStep.entB_zero _ _ _ _ _ rfl, dif_pos ⟨p.2, p'.2⟩]
  rfl

theorem lamY_zero (n : ℕ) (ex : ℕ → ℕ) : LocE.lamY P (qOf P) n 0 ex = stdAt E n P := by
  ext v
  unfold LocE.lamY
  rw [LastSteps.mem_sclLat, mem_stdAt]
  refine forall_congr' fun l => ?_
  have : LocE.scE n ex l.1 = 0 := if_pos l.2
  rw [this, zpow_zero, inv_one, one_mul]

theorem int_entB (k₀ : ℕ) {n : ℕ} (ex : ℕ → ℕ) (j : GLint E n P) :
    IntM P (n + 0) (n + 0) (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0))) :=
  ent_int (n := n) (c := 0) (g := j.1) ((lamY_zero (E := E) (P := P) n ex).symm ▸ j.2)

theorem levG_of_mem (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (k₀ : ℕ) {n r t m : ℕ} (ht : 0 < t) (hn : n = r + m * t)
    (ex : ℕ → ℕ) (j : GLint E n P) (h : redGL n P j ∈ HJ (𝓞 E ⧸ P.asIdeal) n r t m) :
    LevG P r 0 r t (n + 0) (LocE.entB (qOf P) k₀ 0 n 0 n ex ex (j.1.toLinearMap : HomE E (n + 0) (n + 0))) := by
  obtain ⟨h1, h2, h3⟩ := mem_uniUT.1 h
  have hb := mem_btG.1 h1
  have hr : r ≤ n := by omega
  refine ⟨int_entB k₀ ex j, fun p' hp' => ⟨?_, fun p hp hne hz => ?_⟩, fun i p p' a1 a2 a3 => ?_⟩
  · exact (red_entB k₀ ex j ⟨p', by omega⟩ ⟨p', by omega⟩).trans (h3 _ hp')
  · refine (red_entB k₀ ex j ⟨p, hp⟩ ⟨p', by omega⟩).trans ?_
    by_cases hpr : p < r
    · refine h2 _ _ hpr ?_
      have e1 := SymLevelInv.symIdx_cases r 0 p
      have e2 := SymLevelInv.symIdx_cases r 0 p'
      unfold Zs at hz
      simp only
      omega
    · refine hb _ _ ?_
      simp only
      rw [coarse_of_lt hp', coarse_of_le (by omega)]
      omega
  · refine intAt_div_of_redP hq (int_entB k₀ ex j p p' a2 (by omega)) ?_
    refine (red_entB k₀ ex j ⟨p, a2⟩ ⟨p', by omega⟩).trans (hb _ _ ?_)
    simp only
    rw [coarse_rep ht (show r ≤ p by omega) (by omega)]
    by_cases hpr : p' < r
    · rw [coarse_of_lt hpr]
      exact Nat.succ_pos _
    · rw [coarse_rep ht (show r ≤ p' by omega) (by omega)]
      have b1 : (p' - r) / t < i := by
        rw [Nat.div_lt_iff_lt_mul ht]
        omega
      have b2 : i ≤ (p - r) / t := by
        rw [Nat.le_div_iff_mul_le ht]
        omega
      omega

theorem phiG_target (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ψ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ n r t m i c' n' : ℕ} (hm : m = i + 1) (hk : k₀ ≤ n) (ht : 0 < t)
    (hn : n = r + m * t) (j : GLint E n P) (h : redGL n P j ∈ HJ (𝓞 E ⧸ P.asIdeal) n r t m) (x : HomE E (n' + c') (n + 0)) :
    LocE.PhiG (qOf P) ψ χ false k₀ r t m c' n' 0 n ((j.1.toLinearMap : HomE E (n + 0) (n + 0)) ∘ₗ x) *
        LocE.unitV (χ i) ((LinearEquiv.det j.1 : Eˣ) : E) =
      ((lamJ ψ χ n r t m ⟨_, h⟩ : Kˣ) : K) * LocE.PhiG (qOf P) ψ χ false k₀ r t m c' n' 0 n x := by
  subst hm
  rw [phiG_eq, lamJ_eq ψ χ ht hn ⟨_, h⟩
    (red P (LocE.entB (qOf P) k₀ 0 n 0 n (fun i => i + 1) (fun i => i + 1) (j.1.toLinearMap : HomE E (n + 0) (n + 0))))
    (red_entB k₀ (fun i => i + 1) j)]
  refine (phiM_target (c := 0) (k₁ := r) (rS := 0) (r := r) ψ χ hk le_rfl (by rw [hn]; ring)
    (((HJ (𝓞 E ⧸ P.asIdeal) n r t (i + 1)).comap (redGL n P)).map (GLint E n P).subtype) ?_ ?_ (g := j.1) ⟨j, h, rfl⟩ x).trans ?_
  · rintro _ ⟨g, -, rfl⟩
    rw [lamY_zero]
    exact g.2
  · rintro _ ⟨g, hg, rfl⟩
    exact levG_of_mem hq k₀ ht hn _ g hg
  · rw [lamGvS_eq ψ χ le_rfl (int_entB k₀ _ j) hn.ge hn.ge]

end General

theorem phiTop_target_gen : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → ∀ (hP : P ∈ Pr.vGs) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyG Ch (rP0 Ch) ⟨P, hP⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu false m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyG Ch (rP0 Ch) ⟨P, hP⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu false m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP j h x
  have h' : redGL _ P j ∈ HJ (𝓞 X.E ⧸ P.asIdeal) (R.N R.m - 1) R.r R.t R.m := by
    have := rowLevel_unipotent_group Ch ⟨P, hP⟩
    rw [this] at h
    exact h
  have e1 : psi0P Ch P = Ch.psi0 ⟨P, hP⟩ := dif_pos hP
  have e2 : chiP Ch P = chiAt Ch ⟨P, hP⟩ := dif_pos hP
  have hk : R.k ≤ R.N R.m - 1 := by
    have := r_le_X' R
    have := (ranks R (j := 0) (by omega)).2.2.2
    omega
  rw [rowLevel_unipotent_character Ch ⟨P, hP⟩ _ h h']
  unfold PhiTop
  rw [if_pos hP, if_neg Bool.false_ne_true, e1, e2]
  exact phiG_target hq _ _ hm hk R.t_odd.pos (rank_X'_eq R) j h' x

end GlobalTheory.TopTargetGen
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.TopLaw

section Det

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem det_diagMat {κ : Type} [CommRing κ] {n N : ℕ} (hN : N = n + 1) (A : Matrix (Fin n) (Fin n) κ) :
    (diagMat n N A).det = A.det := by
  subst hN
  rw [Matrix.det_succ_row _ (Fin.last n), Finset.sum_eq_single (Fin.last n)]
  · rw [diagMat_of_not_left _ _ (by simp), Matrix.one_apply_eq, Fin.succAbove_last]
    have : (diagMat n (n + 1) A).submatrix Fin.castSucc Fin.castSucc = A := by
      ext i j
      exact diagMat_of_lt (n := n + 1) A (i := i.castSucc) (j := j.castSucc) i.2 j.2
    rw [this, ← two_mul, pow_mul]
    simp
  · intro j _ hj
    rw [diagMat_of_not_left _ _ (by simp), Matrix.one_apply_ne hj.symm, mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem unitV_det_ext (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {n N : ℕ} (hN : N = n + 1) (j : GLint E n P) (k : GLint E N P)
    (h : redGL N P k = redGL N P (extI hN P j)) :
    LocE.unitV χ ((LinearEquiv.det k.1 : Eˣ) : E) = LocE.unitV χ ((LinearEquiv.det j.1 : Eˣ) : E) := by
  refine unitV_congr χ ?_
  rw [(det_glint k).2, (det_glint j).2, ← redGL_val, h, redGL_extI, diagEmb_val, det_diagMat hN, redGL_val]

theorem unitV_inv_det (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {n : ℕ} (k : GLint E n P) :
    LocE.unitV χ⁻¹ ((LinearEquiv.det (k⁻¹).1 : Eˣ) : E) = LocE.unitV χ ((LinearEquiv.det k.1 : Eˣ) : E) := by
  rw [DatumLaw.unitV_eq, DatumLaw.unitV_eq, DatumLaw.extendByZeroOffSubset_mul_left_of_mem_lattice, (det_glint k).2, (det_glint k⁻¹).2]
  refine inv_eq_of_mul_eq_one_left ?_
  rw [← DatumLaw.matrixExtendByZero_mul, ← Matrix.det_mul, ← redGL_val, ← redGL_val, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Matrix.det_one]
  unfold DatumLaw.ext0
  rw [dif_pos isUnit_one]
  simp

theorem phiT_act {a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG) (d' : Deco E b ST SG')
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) (h : GLG (E := E) (n := a) (SG := SG)) (h' : GLG (E := E) (n := b) (SG := SG')) (x : HomE E a b) :
    phiT K (d.act γ h) (d'.act γ' h') (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) = phiT K d d' x := by
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ (forall_congr' fun Q => ?_) rfl rfl
  have key : ∀ y, (y ∈ (d.act γ h).at Q.1 → (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) y ∈ (d'.act γ' h').at Q.1 ∧
      (d'.act γ' h').f Q ((γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) y) = (d.act γ h).f Q y) ↔
      (γ.symm y ∈ d.at Q.1 → x (γ.symm y) ∈ d'.at Q.1 ∧ d'.f Q (x (γ.symm y)) = d.f Q (γ.symm y)) := fun y => by
    show (y ∈ localization₂ _ (gmap γ d.N) → γ' (x (γ.symm y)) ∈ localization₂ _ (gmap γ' d'.N) ∧
      d'.f Q (γ'.symm (γ' (x (γ.symm y)))) = d.f Q (γ.symm y)) ↔ _
    rw [mem_localization_gmap, mem_localization_gmap, LinearEquiv.symm_apply_apply]
  refine ⟨fun H y => ?_, fun H y => (key y).2 (H _)⟩
  have := (key (γ y)).1 (H _)
  rwa [LinearEquiv.symm_apply_apply] at this

end Det

section Frames

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {n : ℕ}
  (Λ : LevFam X.E X.K n Pr.vGs) (Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K)))

def LevAt (P : rowSG Pr sel mu) (κ : GLint X.E n P.1) (c : X.Kˣ) : Prop :=
  (∀ hP : P.1 ∈ Pr.vGs, ∃ h : redGL _ P.1 κ ∈ (Λ ⟨P.1, hP⟩).H, c = (Λ ⟨P.1, hP⟩).lam ⟨_, h⟩) ∧
    ∀ hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K), P.1 ∉ Pr.vGs → ∃ h : κ ∈ (Θ ⟨P.1, hQ⟩).H, c = (Θ ⟨P.1, hQ⟩).lam ⟨κ, h⟩

variable {Λ Θ}

theorem LevAt.inv {P : rowSG Pr sel mu} {κ : GLint X.E n P.1} {c : X.Kˣ} (h : LevAt Λ Θ P κ c) : LevAt Λ Θ P κ⁻¹ c⁻¹ := by
  refine ⟨fun hP => ?_, fun hQ hP => ?_⟩
  · obtain ⟨h1, e⟩ := h.1 hP
    refine ⟨by rw [map_inv]; exact inv_mem h1, ?_⟩
    rw [e, ← map_inv]
    exact congrArg _ (Subtype.ext (map_inv _ _).symm)
  · obtain ⟨h1, e⟩ := h.2 hQ hP
    exact ⟨inv_mem h1, by rw [e, ← map_inv]; rfl⟩

end Frames

section Pass

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {u : Pr.Word} {j : ℕ}
  {Λ : LevFam X.E X.K (R.N j) Pr.vGs} {Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}

def passG (g : FrmG Λ Θ) (p : ChPt (R := R) sel mu u j) (w : Pr.vGs) : GLint X.E (R.N j) w.1 :=
  passFr (d := p.deco.1) g.1.1 g.2.1.1 (liftFr_spec p.deco.2 w) (liftFr_spec (g • p).deco.2 w)

theorem redGL_passG (g : FrmG Λ Θ) (p : ChPt (R := R) sel mu u j) (w : Pr.vGs) : redGL _ w.1 (passG g p w) = g.2.1.1 w :=
  redGL_passFr _ _ _ _

theorem exists_pass (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (g : FrmG Λ Θ) (p : ChPt (R := R) sel mu u j) :
    ∃ (κ : GLQ X.E (R.N j) (rowSG Pr sel mu)) (c : rowSG Pr sel mu → X.Kˣ),
      (∀ P, frsF sel mu (g • p) P = g.1.1 * (frsF sel mu p P * ((κ P)⁻¹).1)) ∧ (∀ P, LevAt Λ Θ P (κ P) (c P)) ∧
        ∏ P, c P = Λ.chr g.2.1 * Θ.chr g.2.2 := by
  classical
  refine ⟨fun P => if h : P.1 ∈ Pr.vGs then
      passG g p ⟨P.1, h⟩
      else g.2.2.1 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩,
    fun P => if h : P.1 ∈ Pr.vGs then (Λ ⟨P.1, h⟩).lam ⟨g.2.1.1 ⟨P.1, h⟩, g.2.1.2 _ (Set.mem_univ _)⟩
      else (Θ ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩).lam ⟨g.2.2.1 _, g.2.2.2 _ (Set.mem_univ _)⟩,
    fun P => ?_, fun P => ⟨fun hP => ?_, fun hQ hP => ?_⟩, ?_⟩
  · unfold frsF
    split_ifs with h
    · simp only [dif_pos h]
      show _ = g.1.1 * (p.deco.1.liftFr ⟨P.1, h⟩ * (((g • p).deco.1.liftFr ⟨P.1, h⟩)⁻¹ * g.1.1 * p.deco.1.liftFr ⟨P.1, h⟩)⁻¹)
      group
    · simp only [dif_neg h]
      exact mul_assoc _ _ _
  · simp only [dif_pos hP]
    have e := redGL_passG g p ⟨P.1, hP⟩
    exact ⟨e ▸ g.2.1.2 _ (Set.mem_univ _), congrArg _ (Subtype.ext e.symm)⟩
  · simp only [dif_neg hP]
    exact ⟨g.2.2.2 _ (Set.mem_univ _), trivial⟩
  · have e2 : Θ.chr g.2.2 = _ := piChar_apply (fun w => (Θ w).H) (fun w => (Θ w).lam) g.2.2
    rw [LevFam.chr_apply, e2]
    refine ((Equiv.Finset.union _ _ hd).prod_comp _).symm.trans ?_
    rw [Fintype.prod_sum_type]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
    · exact dif_pos w.2
    · exact dif_neg (Finset.disjoint_right.1 hd w.2)

end Pass

section Local

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem locTop_extI (P : rowSG Pr sel mu) (j : GLint X.E (R.N R.m - 1) P.1) (y : HomE X.E (R.N (m2 + 1)) (R.N R.m))
    (y' : Sp X.E (R.N (m2 + 1))) :
    locTop Ch sel mu cst m2 P ((extI (N_m_succ R) P.1 j).1.toLinearMap ∘ₗ y) y' =
      PhiTop Ch mu cst.sharp m2 P.1
          (j.1.toLinearMap ∘ₗ (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))) *
        ftY sel mu cst P (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y' := by
  unfold locTop
  congr 2
  · exact LinearMap.ext fun v => prH_sumE (N_m_succ R) _ _ _
  · refine LinearMap.ext fun v => (atNL_last _).trans ((sumE_last (N_m_succ R) _ _ _).trans ?_)
    rw [Units.val_one, one_mul]
    exact (atNL_last (y v)).symm

theorem locTop_target (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hD : P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) {Pl : LevFam X.E X.K R.r Pr.vGs}
    (hlev : (cst.sharp = false ∧ Pl = rP0 Ch) ∨ (cst.sharp = true ∧ Pl = rPsymF Ch)) (c : TopDepth R cst.M)
    {k : GLint X.E (R.N R.m) P.1} {a : X.Kˣ} (hk : LevAt (topLevG Ch Pl) (topLevQ R sel mu c.pos) P k a)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {y' : Sp X.E (R.N (m2 + 1))}
    (hG : P.1 ∈ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i))
    (hQ : P.1 ∉ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i)) :
    locTop Ch sel mu cst m2 P (k.1.toLinearMap ∘ₗ y) y' * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) =
      (a : X.K) * locTop Ch sel mu cst m2 P y y' := by
  classical
  unfold rhoS
  by_cases hP : P.1 ∈ Pr.vGs
  · obtain ⟨h1, e⟩ := hk.1 hP
    obtain ⟨jb, hjb, e1⟩ := (mem_levExt _ _).1 h1
    obtain ⟨j, rfl⟩ := Mem.Col2.redGL_surjective P.1 jb
    have e2 : redGL _ P.1 k = redGL _ P.1 (extI (N_m_succ R) P.1 j) := by rw [redGL_extI]; exact e1.symm
    have e3 : k.1.toLinearMap ∘ₗ y = (k * (extI (N_m_succ R) P.1 j)⁻¹).1.toLinearMap ∘ₗ
        ((extI (N_m_succ R) P.1 j).1.toLinearMap ∘ₗ y) :=
      LinearMap.ext fun v => congrArg k.1 (LinearEquiv.symm_apply_apply (extI (N_m_succ R) P.1 j).1 (y v)).symm
    rw [e3, locTop_inv hm hc hP hq _ (by rw [map_mul, map_inv, e2, mul_inv_cancel]) _ (hG hP), if_pos hP,
      unitV_det_ext _ (N_m_succ R) j k e2, locTop_extI, mul_right_comm, e.trans (levExt_lam _ _ h1 hjb e1.symm)]
    unfold locTop
    rw [← mul_assoc]
    congr 1
    rcases hlev with ⟨hs, rfl⟩ | ⟨hs, rfl⟩
    · rw [hs]
      exact GlobalTheory.TopTargetGen.phiTop_target_gen Ch mu m2 P.1 hm hq hP j hjb _
    · rw [hs]
      exact GlobalTheory.TopLawSym.phiTop_target_sym Ch mu m2 P.1 hm hq hP j hjb _
  · have hPQ := (Finset.mem_union.mp P.2).resolve_left hP
    obtain ⟨h1, e⟩ := hk.2 hPQ hP
    obtain ⟨j, hj, κ, hκ, e1⟩ := (mem_parahoricTimesPrincipalCongruence_iff (N_m_succ R) _ _).1 h1
    have e2 : redGL _ P.1 k = redGL _ P.1 (extI (N_m_succ R) P.1 j) := by
      rw [e1, map_mul, redGL_of_prinCong c.pos hκ, mul_one]
    have e3 : k.1.toLinearMap ∘ₗ y = (extI (N_m_succ R) P.1 j).1.toLinearMap ∘ₗ (κ.1.toLinearMap ∘ₗ y) := by
      rw [e1]
      rfl
    rw [← Model.locTop_invQ hm hc hP (hD hP) c hκ y (hQ hP), e3, if_neg hP, unitV_det_ext _ (N_m_succ R) j k e2, locTop_extI,
      mul_right_comm, e.trans (parahoricTimesPrincipalCongruence_character_eq _ _ c.pos hj hκ h1 e1)]
    unfold locTop
    rw [← mul_assoc]
    congr 1
    exact GlobalTheory.TopLaw.phiTop_target_twist Ch mu m2 P.1 hm hq hP _ _ hPQ j hj _

theorem rhoT_inv (i : ℕ) (P : rowSG Pr sel mu) {n : ℕ} (k : GLint X.E n P.1) :
    rhoT Ch sel mu i P ((LinearEquiv.det (k⁻¹).1 : X.Eˣ) : X.E) = rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) := by
  unfold rhoT rhoS
  rw [← unitV_inv_det]
  split_ifs
  · rfl
  · rw [inv_inv]

theorem coset_sub {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) {Y : Set (Sp X.E (R.N j))}
    (hY : Y ∈ ybSet sel mu cst p.deco.1.N) {v w : Sp X.E (R.N j)} (hv : v ∈ Y) (hw : w ∈ Y) (P : rowSG Pr sel mu) :
    (P.1 ∈ Pr.vGs → (frsF sel mu p P).symm v - (frsF sel mu p P).symm w ∈ stdAt X.E _ P.1) ∧
      (P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M)⁻¹ • ((frsF sel mu p P).symm v - (frsF sel mu p P).symm w) ∈ stdAt X.E _ P.1) := by
  obtain ⟨y, -, rfl⟩ := hY
  have h := (mem_locLat _ _ _ _).1 (sub_mem hv hw) P
  rw [sub_sub_sub_cancel_right] at h
  rw [← map_sub]
  refine ⟨fun hP => ?_, fun hP => ?_⟩
  · simp only [if_pos hP, zpow_zero, inv_one, one_smul] at h
    exact (frsF_mem p P _).1 (by rwa [LinearEquiv.apply_symm_apply])
  · simp only [if_neg hP, zpow_natCast] at h
    rw [← map_smul]
    exact (frsF_mem p P _).1 (by rwa [LinearEquiv.apply_symm_apply])

theorem repY_mem {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} {Y : Set (Sp X.E n)} (hY : Y ∈ ybSet sel mu cst N) : repY Y ∈ Y := by
  obtain ⟨y, -, hY⟩ := hY
  exact Classical.epsilon_spec (p := fun z => z ∈ Y) ⟨y, by rw [hY, Set.mem_ofPred_eq, sub_self]; exact zero_mem _⟩

end Local

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem locTop_source (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {b : L.β (m2 + 1)} {P : rowSG Pr sel mu}
    {k : GLint X.E (R.N (m2 + 1)) P.1} {a : X.Kˣ} (hk : LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P k a)
    (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) {y' y'' : Sp X.E (R.N (m2 + 1))}
    (hG : P.1 ∈ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i))
    (hQ : P.1 ∉ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i))
    (hG' : P.1 ∈ Pr.vGs → k.1 y'' - y' ∈ stdAt X.E _ P.1)
    (hQ' : P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (k.1 y'' - y') ∈ stdAt X.E _ P.1) :
    locTop Ch sel mu cst m2 P (y ∘ₗ k.1.toLinearMap) y'' * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) =
      (a : X.K) * locTop Ch sel mu cst m2 P y y' := by
  have h1 := GlobalTheory.TopLaw.ftY_comp_glint sel mu cst hL.cst_ok P (hL.depthQ P) k (atNL X.E (R.N R.m) (R.N R.m - 1) ∘ₗ y) y' y'' hG hQ hG' hQ'
  have h2 := GlobalTheory.TopSrc.phiTop_level Ch sel mu cst L G m2 hX hPr hL b P k a hk.1 hk.2 (prXp X.E R ∘ₗ y)
  unfold locTop
  rw [mul_right_comm, ← mul_assoc]
  exact congrArg₂ (· * ·) h2 h1

theorem xiTop_law {u : Pr.Word} {b : L.β (m2 + 1)} {Pl : LevFam X.E X.K R.r Pr.vGs} (c : TopDepth R cst.M) (hX : X.Ok) (hPr : Pr.Ok)
    (hsel : IsSel X sel) (hL : L.Ok Ch sel mu cst G m2)
    (hlev : (cst.sharp = false ∧ Pl = rP0 Ch) ∨ (cst.sharp = true ∧ Pl = rPsymF Ch))
    {γ : UF X.E (R.N (m2 + 1))} {γ' : UF X.E (R.N R.m)} {p q : ChPt (R := R) sel mu u (m2 + 1)} {p' q' : TopPt R sel mu u}
    {Y : Set (Sp X.E (R.N (m2 + 1)))} (hp1 : Y ∈ ybSet sel mu cst p.deco.1.N) (hp2 : (fun v => γ.1 v) '' Y ∈ ybSet sel mu cst q.deco.1.N)
    {κ : GLQ X.E (R.N (m2 + 1)) (rowSG Pr sel mu)} {κ' : GLQ X.E (R.N R.m) (rowSG Pr sel mu)} {a a' : rowSG Pr sel mu → X.Kˣ}
    (hκ : ∀ P, frsF sel mu q P = γ.1 * (frsF sel mu p P * ((κ P)⁻¹).1))
    (hκ' : ∀ P, frsF sel mu q' P = γ'.1 * (frsF sel mu p' P * ((κ' P)⁻¹).1))
    (ha : ∀ P, LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P (κ P) (a P))
    (ha' : ∀ P, LevAt (topLevG Ch Pl) (topLevQ R sel mu c.pos) P (κ' P) (a' P)) (x : HomE X.E (R.N (m2 + 1)) (R.N R.m))
    (e0 : phiT X.K q.deco.1 q'.deco.1 (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = phiT X.K p.deco.1 p'.deco.1 x) :
    XiTop Ch sel mu cst m2 q ((fun v => γ.1 v) '' Y) q' (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) *
        ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) *
          rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E)) =
      (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K) * XiTop Ch sel mu cst m2 p Y p' x := by
  unfold TopStep.XiTop
  rw [e0, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  obtain ⟨v, hv, ev⟩ := repY_mem hp2
  have e1 : inFr (frsF sel mu q P) (frsF sel mu q' P) (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) =
      (κ' P).1.toLinearMap ∘ₗ (inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap) := by
    rw [hκ, hκ']
    refine LinearMap.ext fun w => ?_
    show (κ' P).1 ((frsF sel mu p' P).symm (γ'.1.symm (γ'.1 (x (γ.1.symm (γ.1 (frsF sel mu p P (((κ P)⁻¹).1 w)))))))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  have e2 : ((κ P)⁻¹).1 ((frsF sel mu q P).symm (repY ((fun v => γ.1 v) '' Y))) = (frsF sel mu p P).symm v := by
    rw [hκ, ← ev]
    show (κ P).1.symm ((κ P).1 ((frsF sel mu p P).symm (γ.1.symm (γ.1 v)))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hs := coset_sub p hp1 hv (repY_mem hp1) P
  rw [← e2] at hs
  have h1 := locTop_source hX hPr hL (ha P).inv (inFr (frsF sel mu p P) (frsF sel mu p' P) x)
    (repY_int p hp1) (Model.repY_intQ p hp1) hs.1 hs.2
  have h2 := locTop_target (Ch := Ch) hL.hm hL.cst_ok (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2 (hL.depthQ P) hlev c
    (ha' P) (inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap)
    (repY_int q hp2) (Model.repY_intQ q hp2)
  rw [e1, Pi.inv_apply, Pi.inv_apply, rhoT_inv, mul_comm (rhoS _ _ _ _ _ _), ← mul_assoc, h2, mul_assoc, h1, Units.val_mul, mul_assoc]

theorem smul_comp_smul {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] (s t : Kˣ)
    (f : V' →ₗ[K] V') (k : V →ₗ[K] V') (h : V →ₗ[K] V) :
    ((s * t : Kˣ) : K) • (f ∘ₗ k ∘ₗ h) = ((s : K) • f) ∘ₗ k ∘ₗ ((t : K) • h) := by
  rw [LinearMap.comp_smul, LinearMap.comp_smul, LinearMap.smul_comp, smul_smul, Units.val_mul, mul_comm]

theorem topEquiv {u : Pr.Word} {T : ChTh W sel mu u m2} (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    {Pl : LevFam X.E X.K R.r Pr.vGs} (c : TopDepth R cst.M) (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel)
    (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S) (hL : L.Ok Ch sel mu cst G m2)
    (hlev : (cst.sharp = false ∧ Pl = rP0 Ch) ∨ (cst.sharp = true ∧ Pl = rPsymF Ch)) (hT : ChTh.Ok (Ch := Ch) cst T) :
    TopEquiv W Ch sel mu cst L T b hY Pl c := by
  rw [topEquiv_iff_on]
  intro g g₁ p Y p' hp
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  have hp1 : Y ∈ ybSet sel mu cst p.deco.1.N := hp
  have hp2 : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (g • p).deco.1.N := (ybSet_gmap sel mu cst _ g.1.1 Y).2 hp1
  obtain ⟨κ, a, hκ, ha, ea⟩ := exists_pass hd g p
  obtain ⟨κ', a', hκ', ha', ea'⟩ := exists_pass hd g₁ p'
  have key := GlobalTheory.kerOf_gmap_frames T.top (Sall sel mu u) _ (cAof sel mu cst) (cBof sel mu cst u) _ _ _ _ hT.top g.1 g₁.1
    p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p') κ⁻¹ κ'⁻¹ (XiTop Ch sel mu cst m2 p Y p')
    (XiTop Ch sel mu cst m2 (g • p) ((fun v => g.1.1 v) '' Y) (g₁ • p')) (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K)
    ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩
    (GlobalTheory.TopXiInv.xiTop_invariant Ch sel mu cst m2 u hPr hL.hm hL.cst_ok hL.depthQ p Y p' hp1) fun x =>
      xiTop_law c hX hPr hsel hL hlev hp1 hp2 hκ hκ' ha ha' x (phiT_act _ _ _ _ _ _ _)
  have e1 : topDegreeKTwo W Ch sel mu cst T p Y p' = _ := if_pos hp1
  have e2 : topDegreeKTwo W Ch sel mu cst T (g • p) ((fun v => g.1.1 v) '' Y) (g₁ • p') = _ := if_pos hp2
  refine e2.trans ?_
  rw [e1, funext hκ, funext hκ']
  refine key.trans ?_
  rw [ea, ea', mul_inv, ← map_inv (L.levG (m2 + 1) b).chr, ← map_inv (L.levQ (m2 + 1) b).chr]
  exact smul_comp_smul _ _ _ _ _

end Main

end GlobalTheory.TopLaw
