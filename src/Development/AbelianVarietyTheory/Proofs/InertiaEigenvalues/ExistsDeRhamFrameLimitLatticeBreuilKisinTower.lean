module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDROfLinks
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisLimitLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDROfLinksStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLatticeFrameOfLinkedPreframe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLatticeFrameOfLinkedPreframe
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.BKLim

theorem frame_of_links : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r) → ∃ F₀ : Frame bk N d fun g => (ρ g).val, F₀.toPre = P := by
  intro l _ K bk d N ρ tw F P r hL
  obtain ⟨u, hu⟩ := P.unit
  obtain ⟨Ti, hT1, hT2⟩ : ∃ Ti : Matrix (Fin d) (Fin d) (WCb l), P.T * Ti = 1 ∧ Ti * P.T = 1 :=
    ⟨↑u⁻¹, by rw [← hu]; exact u.mul_inv, by rw [← hu]; exact u.inv_mul⟩
  have key : ∀ (g : ↥(GK K)) (i j : Fin d), ∃ a : Ainf l,
      (Ti * zW (ρ g).val * P.T.map (galW l (g : GQ l))) i j
        = inclW l (1 * a) := by
    intro g i j
    refine GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by simp) r _ ?_
    intro n
    obtain ⟨m, hnm, R, G, hc, hd⟩ := hL n
    obtain ⟨σ, hσ⟩ : ∃ σ : WCb l →+* WCb l, ∀ x, σ x = galW l (g : GQ l) x := ⟨((galW l (g : GQ l)).toRingEquiv : WCb l →+* WCb l), fun _ => rfl⟩
    have hσf : (⇑(galW l (g : GQ l)) : WCb l → WCb l) = ⇑σ := funext fun x => (hσ x).symm
    set π := Ideal.Quotient.mk (Ideal.span {((l : WCb l) ^ n)}) with hπ
    have hq : ∀ x y : WCb l, (l : WCb l) ^ n ∣ x - y → π x = π y := fun x y h =>
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h)
    have hM : ∀ {a b : Type} (A B : Matrix a b (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A - B) i j) → A.map π = B.map π := fun A B h => by
      ext i j; exact hq _ _ (by simpa using h i j)
    have hσd : ∀ x : WCb l, (l : WCb l) ^ n ∣ x → (l : WCb l) ^ n ∣ σ x := fun x ⟨y, hy⟩ =>
      ⟨σ y, by rw [hy, map_mul, map_pow, map_natCast]⟩
    have hσz : ∀ {a b : Type} (M : Matrix a b ℤ_[l]), (zW M).map σ = zW M := fun M => by
      ext i j; simp [zW, hσ]
    have hMM : ∀ {a b b' c : Type} [Fintype b] [Fintype b'] (A : Matrix a b (WCb l)) (B : Matrix b c (WCb l))
        (C : Matrix a b' (WCb l)) (D : Matrix b' c (WCb l)),
        (∀ i j, (l : WCb l) ^ n ∣ (A * B - C * D) i j) → A.map π * B.map π = C.map π * D.map π := by
      intro a b b' c _ _ A B C D h
      rw [← Matrix.map_mul, ← Matrix.map_mul]; exact hM _ _ h
    set T' := (F m).T
    set ε' := (F m).ε g
    set Pi := tw.Pi m
    have Ga := (F m).gal g
    rw [hσf] at Ga
    rw [hσf]
    have E1 : (zW Pi).map π * T'.map π = P.T.map π * (R.map bk.evW).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]; exact hM _ _ hc
    have E1σ : (zW Pi).map π * (T'.map σ).map π = (P.T.map σ).map π * ((R.map bk.evW).map σ).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul]
      apply hM
      intro i j
      have h1 : zW Pi * T'.map σ - P.T.map σ * (R.map bk.evW).map σ = (zW Pi * T' - P.T * R.map bk.evW).map σ := by
        rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, hσz]
      rw [h1, Matrix.map_apply]; exact hσd _ (hc i j)
    have E2 : (zW Pi).map π * (zW (tw.ρ' m g).val).map π = (zW (ρ g).val).map π * (zW Pi).map π := by
      apply hMM
      intro i j
      have h1 : zW Pi * zW (tw.ρ' m g).val - zW (ρ g).val * zW Pi = zW (Pi * (tw.ρ' m g).val - (ρ g).val * Pi) := by
        simp only [zW]; rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]
      rw [h1]
      have h2 := map_dvd (algebraMap ℤ_[l] (WCb l)) ((pow_dvd_pow (l : ℤ_[l]) hnm).trans ((tw.onto m).equi g i j))
      simpa [zW] using h2
    have E3 : ((R.map bk.evW).map σ).map π * ((G.map bk.evW).map σ).map π
        = (((l : WCb l) ^ r) • (1 : Matrix (Fin d) (Fin d) (WCb l))).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul]
      apply hM
      intro i j
      have h1 : (((R * G).map bk.evW).map σ - ((l : WCb l) ^ r) • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j
          = σ (bk.evW ((R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j)) := by
        simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, map_sub]
        split_ifs <;> simp
      rw [h1]
      exact hσd _ (by simpa using map_dvd bk.evW (hd i j))
    have He : P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π) = (zW (ρ g).val).map π * (P.T.map σ).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT1, Matrix.one_mul]
    have GaP : (zW (tw.ρ' m g).val).map π * (T'.map σ).map π = T'.map π * (ε'.map (inclW l)).map π := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, Ga]
    have C1 : P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π)
        = P.T.map π * ((R.map bk.evW).map π * (ε'.map (inclW l)).map π) := by
      calc P.T.map π * ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π)
          = (P.T.map π * (Ti * zW (ρ g).val * P.T.map σ).map π) * ((R.map bk.evW).map σ).map π := (Matrix.mul_assoc _ _ _).symm
        _ = (zW (ρ g).val).map π * ((P.T.map σ).map π * ((R.map bk.evW).map σ).map π) := by rw [He, Matrix.mul_assoc]
        _ = (zW (ρ g).val).map π * ((zW Pi).map π * (T'.map σ).map π) := by rw [E1σ]
        _ = ((zW Pi).map π * (zW (tw.ρ' m g).val).map π) * (T'.map σ).map π := by rw [E2, Matrix.mul_assoc]
        _ = (zW Pi).map π * (T'.map π * (ε'.map (inclW l)).map π) := by rw [Matrix.mul_assoc, GaP]
        _ = P.T.map π * ((R.map bk.evW).map π * (ε'.map (inclW l)).map π) := by rw [← Matrix.mul_assoc, E1, Matrix.mul_assoc]
    have hTi : Ti.map π * P.T.map π = 1 := by
      rw [← Matrix.map_mul, hT2, Matrix.map_one _ (map_zero _) (map_one _)]
    have C2 : (Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π := by
      calc _ = (Ti.map π * P.T.map π) *
            ((Ti * zW (ρ g).val * P.T.map σ).map π * ((R.map bk.evW).map σ).map π) := by rw [hTi, Matrix.one_mul]
        _ = _ := by rw [Matrix.mul_assoc, C1, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
    have C3 : (Ti * zW (ρ g).val * P.T.map σ).map π * (((R.map bk.evW).map σ).map π * ((G.map bk.evW).map σ).map π)
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π * ((G.map bk.evW).map σ).map π := by
      rw [← Matrix.mul_assoc, C2]
    rw [E3] at C3
    have hR : (R.map bk.ev).map (inclW l) = R.map bk.evW := by ext; rfl
    have hG : (G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l) = (G.map bk.evW).map σ := by
      ext; simp [BK.evW, hσ, galW_inclW]
    have hY : ((R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l)).map π
        = (R.map bk.evW).map π * (ε'.map (inclW l)).map π * ((G.map bk.evW).map σ).map π := by
      simp only [Matrix.map_mul, hR, hG]
    refine ⟨(R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)) i j, ?_⟩
    have C4 : (((l : WCb l) ^ r) • (Ti * zW (ρ g).val * P.T.map σ)).map π
        = ((R.map bk.ev * ε' * G.map fun x => Per.σA (g : GQ l) (bk.ev x)).map (inclW l)).map π := by
      rw [hY, ← C3, ← Matrix.map_mul, Matrix.mul_smul, mul_one]
    have C5 := congrFun (congrFun C4 i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at C5
    rw [one_mul]
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 C5)
  choose ε hε using key
  refine ⟨{ toPre := P, ε := fun g => Matrix.of (ε g), gal := fun g => ?_ }, rfl⟩
  have h1 : (Matrix.of (ε g)).map (inclW l) = Ti * zW (ρ g).val * P.T.map (galW l (g : GQ l)) := by
    ext i j; rw [Matrix.map_apply, Matrix.of_apply, hε g i j, one_mul]
  show zW (ρ g).val * P.T.map (galW l (g : GQ l)) = P.T * (Matrix.of (ε g)).map (inclW l)
  rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hT1, Matrix.one_mul]

end GlobalTheory.BKLim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLatticeFrameOfLinkedPreframeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisinLatticeFrame_of_linked_preframe : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (P : Pre bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk P.T (F m).T (tw.Pi m) n r) → ∃ F₀ : Frame bk N d fun g => (ρ g).val, F₀.toPre = P := by
  first | exact @GlobalTheory.BKLim.frame_of_links | exact GlobalTheory.BKLim.frame_of_links | (intros; apply GlobalTheory.BKLim.frame_of_links <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFrameIsCrOfLinkedTower
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFrameIsCrOfLinkedTower
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.CrLimit

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem exists_smul_of_dvd {R : Type} [CommRing R] {m n : Type} (c : R) (M : Matrix m n R)
    (h : ∀ i j, c ∣ M i j) : ∃ M' : Matrix m n R, M = c • M' := by
  choose M' hM' using h
  exact ⟨Matrix.of M', by ext i j; simp [hM']⟩

theorem ev_X_dvd_gal (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    bk.ev X ∣ Per.σA (g : GQ l) (bk.ev s) - bk.ev s := by
  obtain ⟨c, hc⟩ := (GlobalTheory.BSP.galois_discMap l K bk).1 (g : GQ l)
  obtain ⟨t, w, e⟩ : ∃ (t : bk.S) (w : Wq l bk.a), s = X * t + C w := ⟨_, _, eq_X_mul_shift_add_const s⟩
  subst e
  rw [map_add (f := _), map_mul, map_add (f := _), map_mul, bk.ev_C, bk.gal_w, hc]
  exact ⟨c * Per.σA (g : GQ l) (bk.ev t) - bk.ev t, by ring⟩

theorem isUnit_inclW_ev_X (bk : BK K) : IsUnit (inclW l (bk.ev X)) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [bk.ev_X, inclW, WittVector.map_teichmuller, WittVector.teichmuller_coeff_zero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 (GlobalTheory.BSP.FlatDisc.flat_ne_zero bk)

end GlobalTheory.BKLim.CrLimit

namespace GlobalTheory.BKLim.CrLimit

theorem isCr_of_link : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsCr) → F₀.IsCr := by
  intro l _ K bk d N ρ tw F F₀ r hlink hcr g i j
  suffices hx : ∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * inclW l ((F₀.ε g - 1) i j) -
      inclW l (bk.ev X * a) by
    obtain ⟨a, ha⟩ := GlobalTheory.T.ainf_principal_ideal_saturated_closed l (bk.ev X) (isUnit_inclW_ev_X bk) r (inclW l ((F₀.ε g - 1) i j)) hx
    exact ⟨a, inclW_injective ha⟩
  intro n
  obtain ⟨m, hnm, R, G, hT, hRG⟩ := hlink n
  have hk := GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked l K bk N N d (tw.d' m) n (fun g => (ρ g).val) (fun g => (tw.ρ' m g).val) F₀ (F m)
    (tw.Pi m) R (fun g i j => (pow_dvd_pow _ hnm).trans ((tw.onto m).equi g i j)) hT
  set σ := Per.σA (g : GQ l) with hσ
  set A := R.map bk.ev with hA
  set B := G.map bk.ev with hB
  set ε₀ := F₀.ε g with hε₀
  set ε' := (F m).ε g with hε'
  obtain ⟨D, hD⟩ := exists_smul_of_dvd ((l : Ainf l) ^ n) (ε₀ * A.map σ - A * ε') (hk g)
  obtain ⟨P, hP⟩ := exists_smul_of_dvd ((l : Ainf l) ^ n) (A * B - (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)))
    (fun i j => by
      have h := map_dvd bk.ev (hRG i j)
      have e : (A * B - (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j =
          bk.ev ((R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) := by
        rw [hA, hB, ← Matrix.map_mul]
        simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub,
          map_mul, map_pow, map_natCast]
        split_ifs <;> simp
      rw [e]
      simpa only [map_pow, map_natCast] using h)
  obtain ⟨Z1, hZ1⟩ := exists_smul_of_dvd (bk.ev X) (ε' - 1) (hcr m g)
  obtain ⟨Z2, hZ2⟩ := exists_smul_of_dvd (bk.ev X) (B.map σ - B) (fun i j => by
    simpa only [hB, Matrix.sub_apply, Matrix.map_apply] using ev_X_dvd_gal bk g (G i j))
  have h1 : ε₀ * A.map σ = A * ε' + (l : Ainf l) ^ n • D := (sub_eq_iff_eq_add').1 hD
  have h2 : A * B = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P :=
    (sub_eq_iff_eq_add').1 hP
  have h3 : A.map σ * B.map σ = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P.map σ := by
    rw [← Matrix.map_mul, h2]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_pow, map_natCast]
    split_ifs <;> simp
  have h4 : ε' = 1 + bk.ev X • Z1 := (sub_eq_iff_eq_add').1 hZ1
  have h5 : B.map σ = B + bk.ev X • Z2 := (sub_eq_iff_eq_add').1 hZ2
  have e1 : ε₀ * (A.map σ * B.map σ) = (l : Ainf l) ^ r • ε₀ + (l : Ainf l) ^ n • (ε₀ * P.map σ) := by
    rw [h3, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
  have e2 : ε₀ * (A.map σ * B.map σ) = A * ε' * B.map σ + (l : Ainf l) ^ n • (D * B.map σ) := by
    rw [← Matrix.mul_assoc, h1, Matrix.add_mul, Matrix.smul_mul]
  have e3 : A * ε' * B.map σ = A * B.map σ + bk.ev X • (A * Z1 * B.map σ) := by
    rw [h4, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e4 : A * B.map σ = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P +
      bk.ev X • (A * Z2) := by
    rw [h5, Matrix.mul_add, h2, Matrix.mul_smul]
  have key : (l : Ainf l) ^ r • (ε₀ - 1) = (l : Ainf l) ^ n • (P + D * B.map σ - ε₀ * P.map σ) +
      bk.ev X • (A * Z1 * B.map σ + A * Z2) := by
    have h := e1.symm.trans e2
    rw [e3, e4] at h
    refine eq_of_sub_eq_zero ?_
    rw [← sub_eq_zero.2 h, smul_sub, smul_sub, smul_add, smul_add]
    abel
  have hij := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at hij
  refine ⟨(A * Z1 * B.map σ + A * Z2) i j, ?_⟩
  have hd : (l : Ainf l) ^ n ∣ (l : Ainf l) ^ r * (ε₀ - 1) i j - bk.ev X * (A * Z1 * B.map σ + A * Z2) i j :=
    ⟨(P + D * B.map σ - ε₀ * P.map σ) i j, by
      simp only [Matrix.add_apply, Matrix.sub_apply] at hij ⊢
      linear_combination hij⟩
  simpa only [map_sub, map_mul, map_pow, map_natCast] using map_dvd (inclW l) hd

end GlobalTheory.BKLim.CrLimit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFrameIsCrOfLinkedTowerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinFrame_isCr_of_linked_tower : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsCr) → F₀.IsCr := by
  first | (exact @GlobalTheory.BKLim.CrLimit.isCr_of_link) | (exact GlobalTheory.BKLim.CrLimit.isCr_of_link) | (intros; apply GlobalTheory.BKLim.CrLimit.isCr_of_link  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTower
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem limit_frame_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val), (∀ n, (F n).IsDR) → ∃ F₀ : Frame bk N d (fun g => (ρ g).val), F₀.IsDR ∧ ((∀ n, (F n).IsCr) → F₀.IsCr) ∧ ∃ r, ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
  intro l _ K bk τ hτ d N ρ tw F hDR
  obtain ⟨P, r, hP⟩ := GlobalTheory.T.exists_breuilKisin_basis_limit_lattice l K bk τ hτ d N ρ tw (fun n => (F n).toPre)
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.T.exists_breuilKisinLatticeFrame_of_linked_preframe l K bk d N ρ tw F P r hP
  have hL : ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
    subst hF₀
    exact hP
  exact ⟨F₀, GlobalTheory.T.isDR_of_links' l K bk d N ρ tw F F₀ r hL hDR,
    fun hCr => GlobalTheory.T.breuilKisinFrame_isCr_of_linked_tower l K bk d N ρ tw F F₀ r hL hCr, r, hL⟩

end GlobalTheory.BKLim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFrameLimitLatticeBreuilKisinTowerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRhamFrame_limitLattice_breuilKisinTower : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val), (∀ n, (F n).IsDR) → ∃ F₀ : Frame bk N d (fun g => (ρ g).val), F₀.IsDR ∧ ((∀ n, (F n).IsCr) → F₀.IsCr) ∧ ∃ r, ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
  first | (exact @GlobalTheory.BKLim.limit_frame_exists) | (exact GlobalTheory.BKLim.limit_frame_exists) | (intros; apply GlobalTheory.BKLim.limit_frame_exists  <;> assumption)
end
