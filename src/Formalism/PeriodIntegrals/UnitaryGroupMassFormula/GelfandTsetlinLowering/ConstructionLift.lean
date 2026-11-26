module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftFock
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTuple

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftAsm
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem lm_natW_anti {k : ℕ} (mu : DomWeight k) : Antitone mu.natW := by
  intro i j hij
  have := mu.anti hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)

theorem lm_fockF_eq_sum {σ : Type*} (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ s, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  apply Finset.sum_subset hs
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm]
  simp

theorem lm_fockF_add {σ : Type*} (f1 f2 g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f1 + f2) g = Formalism.REAL.fockF f1 g + Formalism.REAL.fockF f2 g := by
  classical
  rw [lm_fockF_eq_sum (f1 + f2) g (f1.support ∪ f2.support) MvPolynomial.support_add,
    lm_fockF_eq_sum f1 g _ Finset.subset_union_left, lm_fockF_eq_sum f2 g _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem lm_fockF_smul {σ : Type*} (a : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (a • f) g = a * Formalism.REAL.fockF f g := by
  classical
  rw [lm_fockF_eq_sum (a • f) g f.support MvPolynomial.support_smul, Formalism.REAL.fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem lm_fockF_zsmul {σ : Type*} (a : ℤ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (a • f) g = a * Formalism.REAL.fockF f g := by
  rw [← Int.cast_smul_eq_zsmul ℂ, lm_fockF_smul]

theorem lm_fockF_finsum {σ ι : Type*} (s : Finset ι) (y : ι → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ)
    (h0 : ∀ i ∈ s, Formalism.REAL.fockF (y i) g = 0) : Formalism.REAL.fockF (∑ i ∈ s, y i) g = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Formalism.REAL.fockF]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, lm_fockF_add, h0 i (Finset.mem_insert_self _ _),
      ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj)), add_zero]

theorem lm_rowDiv_sub {R : Type*} [CommRing R] {r m : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b k (f - g) = rowDiv R a b k f - rowDiv R a b k g := by
  simp only [rowDiv, map_sub, Polynomial.coeff_sub]

theorem lm_rowDiv_smul {R : Type*} [CommRing R] {r m : ℕ} (a b : Fin r) (k : ℕ) (c : R)
    (f : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]

theorem lm_applyWord_sub_smul {R : Type*} [CommRing R] {r m : ℕ} (w : List (Fin r × Fin r × ℕ)) (c : R)
    (f g : MvPolynomial (Fin r × Fin m) R) :
    applyWord R w (f - c • g) = applyWord R w f - c • applyWord R w g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (f - c • g)) =
      rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) - c • rowDiv R x.1 x.2.1 x.2.2 (applyWord R w g)
    rw [ih, lm_rowDiv_sub, lm_rowDiv_smul]

theorem lm_isWH_map {σ M : Type*} [AddCommMonoid M] (w : σ → M) (f : MvPolynomial σ ℤ) (d : M)
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w (map (Int.castRingHom ℂ) f) d := by
  intro m hm
  apply hf
  rw [coeff_map] at hm
  intro h0
  apply hm
  rw [h0, map_zero]

theorem lm_last_of_row {N : ℕ} (hN : 0 < N) (f : MvPolynomial (Fin N × Fin N) ℂ) (ω : Fin N → ℕ)
    (hf : IsWeightedHomogeneous (rowW N N) f ω) :
    IsWeightedHomogeneous (lastW N) f (ω ⟨N - 1, by omega⟩) := by
  intro m hm
  rw [← hf hm, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [lastW, rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Fin.ext_iff]
  by_cases hv : v.1.1 + 1 = N
  · rw [if_pos hv, if_pos (by omega)]
  · rw [if_neg hv, if_neg (by omega)]

theorem lm_liftWt_last {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) (ω : Fin n → ℕ) :
    liftWt h lam mu ω ⟨N - 1, by omega⟩ = dLast lam mu := by
  unfold liftWt
  rw [dite_eq_right (by simp; omega)]

theorem lm_liftWt_inj {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) {ω ω' : Fin n → ℕ}
    (he : liftWt h lam mu ω = liftWt h lam mu ω') : ω = ω' := by
  funext a
  have := congrFun he (eRow h a)
  have ha : (eRow h a).1 < n := a.isLt
  simp only [liftWt, ha, dif_pos] at this
  simpa [eRow] using this

theorem lm_map_initMinor {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m) :
    map (Int.castRingHom ℂ) (initMinor ℤ (n := m) I hs) = initMinor ℂ I hs := by
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem lm_map_xi {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    map (Int.castRingHom ℂ) (xi ℤ h lam sg) = xi ℂ h lam sg := by
  unfold xi
  simp only [map_prod, map_mul, map_pow, lm_map_initMinor, Formalism.UG.P.wlocal_map_lpMinor]

theorem lm_map_ext {n : ℕ} (sg : DomWeight n) :
    map (Int.castRingHom ℂ) (extremal ℤ n sg) = extremal ℂ n sg := by
  unfold extremal
  exact Formalism.UG.P.wlocal_map_hw _ _ _

theorem liftMod_asm (hZ : CapelliZ) (hV : ZScalarVanish) (hN : Numbers) (hX : XiFacts)
    (equivariant_divisibility : EqvDiv) (equivariant_partial_weight : EqvRowWt) (hdecP : Decomp) (hZC : ZComm) (hFD : FockDetect)
    (tuple_decomposition_formula : TupleCore) : LiftMod := by
  intro n N h lam sg hI io0 hE hx _hW
  obtain ⟨Z, -, hZa⟩ := hZ n N h lam sg hI
  have hc0 : ((cBr h lam sg : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hN n N h lam sg hI).1
  set c : ℂ := ((cBr h lam sg : ℤ) : ℂ) with hc
  have hxi0 : xi ℂ h lam sg ≠ 0 := (hX n N h lam sg hI).1
  have hext : extremal ℂ n sg ∈ nablaSq ℂ n sg := hwMem ℂ n n le_rfl sg.natW (lm_natW_anti sg)
  obtain ⟨hZmem, hZdiv, hZwt⟩ := hZC n N h lam Z
    (fun mu hmu φ hφ => ⟨_, hZa mu hmu φ hφ⟩)
  have hZio : ∀ s ∈ nablaSq ℂ n sg, Z (io0 s) = c • io0 s := fun s hs => hZa sg hI io0 hE s hs
  have hO : ∀ o ∈ OtherPart h lam sg, Z o = 0 := by
    intro o ho
    have hle : OtherPart h lam sg ≤ LinearMap.ker Z := by
      unfold OtherPart
      refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun hne => iSup_le fun hw =>
        iSup_le fun φ => iSup_le fun hφ => ?_
      rintro _ ⟨t, ht, rfl⟩
      rw [LinearMap.mem_ker, hZa mu hmu φ hφ t ht, hV n N h lam sg mu hI hmu hne hw, Int.cast_zero,
        zero_smul]
    exact hle ho
  have hdec := hdecP n N h lam sg hI io0 hE (by rw [hx]; exact hxi0)
  have hcrit : ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (lastW N) f (dLast lam sg) →
      ∀ s ∈ nablaSq ℂ n sg, Z f = c • io0 s → f - io0 s ∈ OtherPart h lam sg := by
    intro f hf hfl s _ hZf
    obtain ⟨u, hu, ho⟩ := hdec f hf hfl
    have h1 : Z f = c • io0 u := by
      have := hO _ ho
      rw [map_sub, hZio u hu, sub_eq_zero] at this
      exact this
    have h2 : io0 u = io0 s := by
      rw [h1] at hZf
      exact smul_right_injective _ hc0 hZf
    rwa [← h2]
  have hZim : ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (lastW N) f (dLast lam sg) →
      ∃ u ∈ nablaSq ℂ n sg, Z f = io0 u := by
    intro f hf hfl
    obtain ⟨u, hu, ho⟩ := hdec f hf hfl
    refine ⟨c • u, Submodule.smul_mem _ _ hu, ?_⟩
    have := hO _ ho
    rw [map_sub, hZio u hu, sub_eq_zero] at this
    rw [this, map_smul]
  have hIoW : ∀ w : List (Fin n × Fin n × ℕ), OffDiag w → ∀ s ∈ nablaSq ℂ n sg,
      applyWord ℂ w s ∈ nablaSq ℂ n sg ∧
        io0 (applyWord ℂ w s) = applyWord ℂ (liftWord h w) (io0 s) := by
    intro w
    induction w with
    | nil => intro _ s hs; exact ⟨hs, rfl⟩
    | cons x w ih =>
      intro hw s hs
      have hw' : OffDiag w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
      obtain ⟨h1, h2⟩ := ih hw' s hs
      refine ⟨rowDivStable ℂ n n sg.natW x.1 x.2.1 x.2.2 _ h1, ?_⟩
      show io0 (rowDiv ℂ x.1 x.2.1 x.2.2 (applyWord ℂ w s)) =
        rowDiv ℂ (eRow h x.1) (eRow h x.2.1) x.2.2 (applyWord ℂ (liftWord h w) (io0 s))
      rw [equivariant_divisibility n N h sg lam io0 hE x.1 x.2.1 (hw x (by simp)) x.2.2 _ h1, h2]
  have hZW : ∀ w : List (Fin n × Fin n × ℕ), OffDiag w → ∀ f ∈ nablaSq ℂ N lam,
      applyWord ℂ (liftWord h w) f ∈ nablaSq ℂ N lam ∧
        Z (applyWord ℂ (liftWord h w) f) = applyWord ℂ (liftWord h w) (Z f) := by
    intro w
    induction w with
    | nil => intro _ f hf; exact ⟨hf, rfl⟩
    | cons x w ih =>
      intro hw f hf
      have hw' : OffDiag w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
      obtain ⟨h1, h2⟩ := ih hw' f hf
      refine ⟨rowDivStable ℂ N N lam.natW _ _ x.2.2 _ h1, ?_⟩
      show Z (rowDiv ℂ (eRow h x.1) (eRow h x.2.1) x.2.2 (applyWord ℂ (liftWord h w) f)) =
        rowDiv ℂ (eRow h x.1) (eRow h x.2.1) x.2.2 (applyWord ℂ (liftWord h w) (Z f))
      rw [hZdiv x.1 x.2.1 (hw x (by simp)) x.2.2 _ h1, h2]
  have hgen : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n),
      shapeDeg sz = sg.natW → ∃ m ∈ nablaSq ℤ N lam,
        map (Int.castRingHom ℂ) m - io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz I)) ∈
          OtherPart h lam sg := by
    intro K sz hsz I hsh
    obtain ⟨M, hM1, hM2, hM3, J0, hJ0c, -, hJ0m⟩ := tuple_decomposition_formula n N h lam sg hI K sz hsz hsh
    have hbm : ∀ J, map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J) ∈ nablaSq ℂ n sg := by
      intro J
      have := bidetMem ℤ n n K sz hsz J
      rw [hsh] at this
      exact dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW _ this
    have hMm : ∀ J, map (Int.castRingHom ℂ) (M J) ∈ nablaSq ℂ N lam := fun J =>
      dualWeylMap ℤ ℂ (Int.castRingHom ℂ) N N lam.natW _ (hM1 J).1
    have hMl : ∀ J, IsWeightedHomogeneous (lastW N) (map (Int.castRingHom ℂ) (M J)) (dLast lam sg) := by
      intro J
      have := lm_last_of_row (N := N) (by omega) _ _ (lm_isWH_map _ _ _ (hM1 J).2.1)
      rwa [lm_liftWt_last] at this
    have hxiW : IsWeightedHomogeneous (rowW N N) (xi ℂ h lam sg) (liftWt h lam sg sg.natW) := by
      have := lm_isWH_map _ _ _ (hM1 J0).2.1
      rwa [hJ0m, lm_map_xi, hJ0c] at this

    set Δ : (∀ k, Fin (sz k) → Fin n) → MvPolynomial (Fin N × Fin N) ℂ := fun J =>
      Z (map (Int.castRingHom ℂ) (M J)) - c • io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J)) with hΔ
    have hΔim : ∀ J, ∃ u ∈ nablaSq ℂ n sg, Δ J = io0 u := by
      intro J
      obtain ⟨u, hu, hZu⟩ := hZim _ (hMm J) (hMl J)
      refine ⟨u - c • map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J),
        Submodule.sub_mem _ hu (Submodule.smul_mem _ _ (hbm J)), ?_⟩
      simp only [hΔ]
      rw [map_sub, map_smul, hZu]
    have hΔorth : ∀ J, Formalism.REAL.fockF (Δ J) (xi ℂ h lam sg) = 0 := by
      intro J
      by_cases hJ : tupCnt J = sg.natW
      · obtain ⟨ε, hb, hm⟩ := hM3 J hJ
        have h0 : Δ J = 0 := by
          simp only [hΔ, hb, hm, map_zsmul, lm_map_xi, lm_map_ext]
          rw [← hx, hZio _ hext, smul_comm c ε, sub_self]
        rw [h0]
        simp [Formalism.REAL.fockF]
      · have hw1 : IsWeightedHomogeneous (rowW N N) (Δ J) (liftWt h lam sg (tupCnt J)) := by
          have a1 := hZwt _ _ (hMm J) (lm_isWH_map _ _ _ (hM1 J).2.1)
          have a2 := equivariant_partial_weight n N h lam sg hI io0 hE (tupCnt J) _ (hbm J)
            (lm_isWH_map _ _ _ (hM1 J).2.2)
          have := Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr a1)
            (Submodule.smul_mem _ c ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr a2))
          exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp this
        exact fockWeightOrth _ _ (rowW N N) _ _ _ _
          (fun he => hJ (lm_liftWt_inj h lam sg he)) hw1 hxiW
    obtain ⟨u, hu, hΔu⟩ := hΔim I
    have hzero : io0 u = 0 := by
      refine hFD n N h lam sg hI io0 hE hx u hu ?_
      intro w hw
      obtain ⟨d, hd1, hd2⟩ := hM2 I w hw
      rw [← hΔu]
      have e1 : applyWord ℂ (liftWord h w) (Z (map (Int.castRingHom ℂ) (M I))) =
          d.sum fun J k => k • Z (map (Int.castRingHom ℂ) (M J)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← (hZW w hw _ (hMm I)).2, ← Formalism.UG.P.wlocal_map_applyWord, hd2, Finsupp.sum, Finsupp.sum,
          map_sum, map_sum]
        simp only [map_zsmul]
      have e2 : applyWord ℂ (liftWord h w) (io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz I))) =
          d.sum fun J k => k • io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← (hIoW w hw _ (hbm I)).2, ← Formalism.UG.P.wlocal_map_applyWord, hd1, Finsupp.sum, Finsupp.sum,
          map_sum, map_sum]
        simp only [map_zsmul]
      have e3 : applyWord ℂ (liftWord h w) (Δ I) = ∑ J ∈ d.support, d J • Δ J := by
        simp only [hΔ]
        rw [lm_applyWord_sub_smul, e1, e2, Finsupp.sum, Finsupp.sum, Finset.smul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [smul_sub, smul_comm c (d J)]
      rw [e3]
      refine lm_fockF_finsum _ _ _ fun J _ => ?_
      rw [lm_fockF_zsmul, hΔorth J, mul_zero]
    refine ⟨M I, (hM1 I).1, hcrit _ (hMm I) (hMl I) _ (hbm I) ?_⟩
    have : Δ I = 0 := by rw [hΔu, hzero]
    rw [hΔ] at this
    exact sub_eq_zero.mp this
  intro s hs
  have hs' : s ∈ Submodule.span ℤ {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
      (I : ∀ k, Fin (sz k) → Fin n), shapeDeg sz = sg.natW ∧ f = bideterminant ℤ sz hsz I} := by
    rw [← standardMonomialSpan n n sg.natW (lm_natW_anti sg)]
    exact hs
  clear hs
  induction hs' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
    exact hgen K sz hsz I hsh
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, hm1, h1⟩ := hx
    obtain ⟨m2, hm2, h2⟩ := hy
    refine ⟨m1 + m2, Submodule.add_mem _ hm1 hm2, ?_⟩
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]
    convert Submodule.add_mem _ h1 h2 using 1
    abel
  | smul a x _ hx =>
    obtain ⟨m, hm, h1⟩ := hx
    refine ⟨a • m, Submodule.smul_mem _ a hm, ?_⟩
    rw [map_zsmul, map_zsmul, map_zsmul, ← smul_sub]
    exact zsmul_mem h1 a

end PI.WGL
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftEqvDiv
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

section SlopeTestRemainingChoices

def tvU {r : ℕ} (a b : Fin r) (hab : a ≠ b) (t : ℂ) : GL (Fin r) ℂ where
  val := Formalism.UG.P.wlocal_E a b t
  inv := Formalism.UG.P.wlocal_E a b (-t)
  val_inv := by
    rw [Formalism.UG.P.wlocal_E_mul_E, if_neg hab, add_neg_cancel, add_zero, Formalism.UG.P.wlocal_E_zero]
  inv_val := by
    rw [Formalism.UG.P.wlocal_E_mul_E, if_neg hab, neg_add_cancel, add_zero, Formalism.UG.P.wlocal_E_zero]

lemma wlocal_E_eq_tv {r : ℕ} (a b : Fin r) (t : ℂ) :
    Formalism.UG.P.wlocal_E a b t = Matrix.transvection a b t := by
  ext i j
  simp [Formalism.UG.P.wlocal_E, Matrix.transvection, Matrix.one_apply]
  rw [Matrix.single_apply]
  exact if_congr (by constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩) rfl rfl

lemma wlocal_E_transpose {r : ℕ} (a b : Fin r) (t : ℂ) :
    (Formalism.UG.P.wlocal_E a b t).transpose = Formalism.UG.P.wlocal_E b a t := by
  ext i j
  simp only [Matrix.transpose_apply, Formalism.UG.P.wlocal_E]
  congr 1
  · exact if_congr eq_comm rfl rfl
  · exact if_congr and_comm rfl rfl

lemma sqAct_tv {r : ℕ} (ν : DomWeight r) (a b : Fin r) (hab : a ≠ b) (t : ℂ) (u : GL (Fin r) ℂ)
    (hu : (u : Matrix (Fin r) (Fin r) ℂ) = Formalism.UG.P.wlocal_E a b t) (f : MvPolynomial (Fin r × Fin r) ℂ) :
    sqAct ℂ r ν u f = Polynomial.eval (C t) (rowGen ℂ a b f) := by
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hu, wlocal_E_eq_tv,
      Matrix.det_transvection_of_ne _ _ hab]
  unfold sqAct detPow
  rw [hdet, one_zpow, Units.val_one, one_smul, hu, wlocal_E_transpose]
  induction f using MvPolynomial.induction_on
  next c => simp [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen]
  next p q hp hq => simp only [map_add (f := _), Polynomial.eval_add, hp, hq]
  next p v hp =>
    rw [map_mul, map_mul, Polynomial.eval_mul, hp]
    congr 1
    obtain ⟨i, j⟩ := v
    simp only [Formalism.GradedWeylDivisibility.rowAct, Formalism.GradedWeylDivisibility.rowGen, MvPolynomial.aeval_X]
    by_cases hi : i = b
    · subst hi
      simp [Formalism.UG.P.wlocal_E, add_mul, Finset.sum_add_distrib, ite_and]
      rw [Finset.sum_eq_single a (fun x _ hx => by simp [hx]) (by simp), if_pos rfl, mul_comm]
    · simp [Formalism.UG.P.wlocal_E, add_mul, Finset.sum_add_distrib, hi]

lemma embGL_tv {n N : ℕ} (h : n + 1 = N) (a b : Fin n) (hab : a ≠ b) (t : ℂ) :
    ((PI.embGL ℂ n N h (tvU a b hab t) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Formalism.UG.P.wlocal_E (eRow h a) (eRow h b) t := by
  subst h
  have he : ∀ x : Fin n, eRow (rfl : n + 1 = n + 1) x = Fin.castSucc x := fun x => Fin.ext rfl
  have hl : ∀ x : Fin n, (Fin.last n = Fin.castSucc x) ↔ False :=
    fun x => ⟨fun e => (Fin.castSucc_lt_last x).ne' e, False.elim⟩
  ext i j
  simp only [he]
  simp [PI.embGL, PI.blkHom, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply, tvU]
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    simp [Formalism.UG.P.wlocal_E, hl]

end SlopeTestRemainingChoices

private theorem coeff_eq_of_eval_lemma {σ τ : Type*}
    (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (P : Polynomial (MvPolynomial σ ℂ)) (Q : Polynomial (MvPolynomial τ ℂ))
    (hPQ : ∀ t : ℂ, φ (P.eval (C t)) = Q.eval (C t)) (k : ℕ) :
    φ (P.coeff k) = Q.coeff k := by
  obtain ⟨d, hdP, hdQ⟩ : ∃ d, P.natDegree < d ∧ Q.natDegree < d :=
    ⟨P.natDegree + Q.natDegree + 1, by omega, by omega⟩
  have hP : ∀ t : ℂ, P.eval (C t) = ∑ i ∈ Finset.range d, t ^ i • P.coeff i := by
    intro t
    rw [Polynomial.eval_eq_sum_range' hdP]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]
  have hQ : ∀ t : ℂ, Q.eval (C t) = ∑ i ∈ Finset.range d, t ^ i • Q.coeff i := by
    intro t
    rw [Polynomial.eval_eq_sum_range' hdQ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, map_pow, mul_comm]
  by_cases hk : k < d
  · refine MvPolynomial.ext _ _ fun m => ?_
    let p : Polynomial ℂ :=
      ∑ i ∈ Finset.range d, Polynomial.monomial i (AddMonoidAlgebra.coeff (φ (P.coeff i)) m)
    let q : Polynomial ℂ :=
      ∑ i ∈ Finset.range d, Polynomial.monomial i (AddMonoidAlgebra.coeff (Q.coeff i) m)
    have hpq : p = q := by
      apply Polynomial.funext
      intro t
      have e := congrArg (AddMonoidAlgebra.coeff · m) (hPQ t)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hP t, hQ t, map_sum] at e
      simp only [map_smul, MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at e
      simp only [p, q, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      simpa [mul_comm] using e
    have e2 := congrArg (fun r : Polynomial ℂ => r.coeff k) hpq
    simpa only [p, q, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply,
      Finset.sum_ite_eq', Finset.mem_range, hk, if_true] using e2
  · have h1 : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 : Q.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [h1, h2, map_zero]

theorem equivariant_divisibility : EqvDiv := by
  intro n N h mu lam φ hφ a b hab k s hs
  unfold IsEqv at hφ
  have hab' : eRow h a ≠ eRow h b := fun he =>
    hab (Fin.ext (by simpa [eRow] using congrArg Fin.val he))
  exact coeff_eq_of_eval_lemma φ (rowGen ℂ a b s) (rowGen ℂ (eRow h a) (eRow h b) (φ s))
    (fun t => by
      have e1 := hφ.2 (tvU a b hab t) s hs
      rwa [sqAct_tv mu a b hab t _ rfl s,
        sqAct_tv lam (eRow h a) (eRow h b) hab' t _ (embGL_tv h a b hab t) (φ s)] at e1) k

end PI.WGL
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.NablaSqLeOfGen
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem nablaSq_le_of_gen (h4 : PI.GTBranch) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N)
    (P : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hP : ∀ (mu : DomWeight n), Interlace h lam mu →
      ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
        ∀ s ∈ nablaSq ℂ n mu, φ s ∈ P) :
    nablaSq ℂ N lam ≤ P := by
  rw [(h4 n N h lam).2]
  refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
  rw [Submodule.map_le_iff_le_comap]
  intro s hs
  exact hP mu hmu φ hφ s hs

theorem comp_gen (hW : EqvRowWt) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (hmu : Interlace h lam mu)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (Z : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (z : ℂ)
    (hz : ∀ s ∈ nablaSq ℂ n mu, Z (φ s) = z • φ s) (ν : Fin N → ℕ) (s : MvPolynomial (Fin n × Fin n) ℂ)
    (hs : s ∈ nablaSq ℂ n mu) :
    Z (weightedHomogeneousComponent (rowW N N) ν (φ s)) =
      weightedHomogeneousComponent (rowW N N) ν (Z (φ s)) := by

  have hterm : ∀ ω : Fin n → ℕ,
      Z (weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s))) =
        z • weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s)) := by
    intro ω
    have hc : weightedHomogeneousComponent (rowW n n) ω s ∈ nablaSq ℂ n mu :=
      dualWeylRowGraded ℂ n n mu.natW ω s hs
    have hhom : IsWeightedHomogeneous (rowW N N)
        (φ (weightedHomogeneousComponent (rowW n n) ω s)) (liftWt h lam mu ω) :=
      hW n N h lam mu hmu φ hφ ω _ hc (weightedHomogeneousComponent_isWeightedHomogeneous ω s)
    by_cases hν : ν = liftWt h lam mu ω
    · subst hν
      rw [hhom.weightedHomogeneousComponent_same]
      exact hz _ hc
    · rw [hhom.weightedHomogeneousComponent_ne ν hν, map_zero, smul_zero]
  have hsum : s = ∑ ω ∈ (weightedHomogeneousComponent_finsupp (w := rowW n n) s).toFinset,
      weightedHomogeneousComponent (rowW n n) ω s := by
    conv_lhs => rw [← finsum_weightedHomogeneousComponent (rowW n n) s]
    exact finsum_eq_sum _ _
  rw [hz s hs, map_smul]
  conv_lhs => rw [hsum]
  conv_rhs => rw [hsum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun ω _ => hterm ω

theorem zComm_of (h4 : PI.GTBranch) (hD : EqvDiv) (hW : EqvRowWt) : ZComm := by
  intro n N h lam Z hZ

  have hcomp : ∀ ν : Fin N → ℕ, ∀ f ∈ nablaSq ℂ N lam,
      Z (weightedHomogeneousComponent (rowW N N) ν f) = weightedHomogeneousComponent (rowW N N) ν (Z f) := by
    intro ν f hf
    have hle := nablaSq_le_of_gen h4 h lam
      (LinearMap.eqLocus (Z ∘ₗ weightedHomogeneousComponent (rowW N N) ν)
        (weightedHomogeneousComponent (rowW N N) ν ∘ₗ Z)) (by
        intro mu hmu φ hφ s hs
        obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
        rw [LinearMap.mem_eqLocus]
        exact comp_gen hW h lam mu hmu φ hφ Z z hz ν s hs)
    have := hle hf
    rw [LinearMap.mem_eqLocus] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    have hle := nablaSq_le_of_gen h4 h lam ((nablaSq ℂ N lam).comap Z) (by
      intro mu hmu φ hφ s hs
      obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
      rw [Submodule.mem_comap, hz s hs]
      exact Submodule.smul_mem _ z (hφ.1 s hs))
    exact hle hf
  · intro a b hab k f hf
    have hle := nablaSq_le_of_gen h4 h lam
      (LinearMap.eqLocus (Z ∘ₗ rowDivL ℂ (eRow h a) (eRow h b) k)
        (rowDivL ℂ (eRow h a) (eRow h b) k ∘ₗ Z)) (by
        intro mu hmu φ hφ s hs
        obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
        rw [LinearMap.mem_eqLocus]
        simp only [LinearMap.comp_apply, rowDivL_apply]
        have hs' : rowDiv ℂ a b k s ∈ nablaSq ℂ n mu := rowDivStable ℂ n n mu.natW a b k s hs
        rw [← hD n N h mu lam φ hφ a b hab k s hs, hz _ hs', hz s hs, rowDiv_smul,
          hD n N h mu lam φ hφ a b hab k s hs])
    have := hle hf
    rw [LinearMap.mem_eqLocus] at this
    simpa only [LinearMap.comp_apply, rowDivL_apply] using this
  · intro ω f hf hhom
    rw [← hhom.weightedHomogeneousComponent_same, hcomp ω f hf]
    exact weightedHomogeneousComponent_isWeightedHomogeneous ω _

end PI.WGL
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDecomp
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem dominant_weight_ext {N : ℕ} (a b : DomWeight N) (hab : a.w = b.w) : a = b := by
  obtain ⟨w, hw⟩ := a
  obtain ⟨w', hw'⟩ := b
  simp only at hab
  subst hab
  rfl

theorem extremal_mem_nablaSq' (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ∈ nablaSq ℂ n mu :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (fun i j hij => Int.toNat_le_toNat (by have := mu.anti hij; omega))

theorem degree_sub_det_shift_nonneg {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (hmu : Interlace h lam mu) : 0 ≤ degZ lam mu - lam.detShift := by
  subst h
  have hle : ∀ i : Fin n, mu.w i ≤ lam.w (Fin.castSucc i) := fun i => (hmu i).1
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hle i)
  have hl : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dite_eq_left (by omega)]
    congr 1
  unfold degZ wsum
  rw [hl, Fin.sum_univ_castSucc]
  linarith

theorem weight_sum_eq_of_last_gap {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu sg : DomWeight n)
    (hmu : Interlace h lam mu) (hsg : Interlace h lam sg) (hd : dLast lam mu = dLast lam sg) :
    wsum mu = wsum sg := by
  have h1 := degree_sub_det_shift_nonneg h lam mu hmu
  have h2 := degree_sub_det_shift_nonneg h lam sg hsg
  unfold dLast at hd
  have h3 : degZ lam mu - lam.detShift = degZ lam sg - lam.detShift := by
    rw [← Int.toNat_of_nonneg h1, ← Int.toNat_of_nonneg h2, hd]
  unfold degZ at h3
  linarith

theorem decomp_of (h4 : PI.GTBranch) (hL : EqvLast) : Decomp := by
  intro n N h lam sg hsg io0 hio hne f hf hfw
  classical
  let T : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nablaSq ℂ n sg).map io0 ⊔ OtherPart h lam sg
  have key : nablaSq ℂ N lam ≤ T.comap (weightedHomogeneousComponent (lastW N) (dLast lam sg)) := by
    rw [(h4 n N h lam).2]
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro s hs
    rw [Submodule.mem_comap, Submodule.mem_comap]
    have hφ' : IsEqv h mu lam φ := hφ
    have hhom := hL n N h lam mu hmu φ hφ' s hs
    by_cases hd : dLast lam mu = dLast lam sg
    · rw [hd] at hhom
      rw [hhom.weightedHomogeneousComponent_same]
      have hw : wsum mu = wsum sg := weight_sum_eq_of_last_gap h lam mu sg hmu hsg hd
      by_cases hmw : mu.w = sg.w
      · have hms : mu = sg := dominant_weight_ext mu sg hmw
        subst hms
        have hboth : ∀ ψ ∈ ({φ, io0} : Set (MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)),
            (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧
            ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
              ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s) := by
          intro ψ hψ
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
          rcases hψ with rfl | rfl
          · exact hφ'
          · exact hio
        obtain ⟨_, c, hc⟩ := (h4 n N h lam).1 mu φ io0 hboth ⟨extremal ℂ n mu, extremal_mem_nablaSq' n mu, hne⟩
        refine Submodule.mem_sup_left ?_
        rw [hc s hs, ← map_smul]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ c hs)
      · refine Submodule.mem_sup_right ?_
        unfold OtherPart
        exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu (Submodule.mem_iSup_of_mem hmw
          (Submodule.mem_iSup_of_mem hw (Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ'
            (Submodule.mem_map_of_mem hs))))))
    · rw [hhom.weightedHomogeneousComponent_ne (dLast lam sg) (Ne.symm hd)]
      exact zero_mem _
  have hfT := key hf
  rw [Submodule.mem_comap, hfw.weightedHomogeneousComponent_same] at hfT
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hfT
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
  refine ⟨u, hu, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

end PI.WGL
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftEqvWt
noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

namespace EqvWt

theorem coeff_aeval_scale {σ : Type} (e : σ → ℂ) (f : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun v => C (e v) * X v) f) m = (m.prod fun v k => e v ^ k) * AddMonoidAlgebra.coeff f m := by
  classical
  refine MvPolynomial.induction_on' f (fun u a => ?_) (fun p q hp hq => ?_)
  · have key : aeval (fun v => C (e v) * X v) (monomial u a) =
        monomial u (a * u.prod fun v k => e v ^ k) := by
      rw [aeval_monomial, monomial_eq]
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
        MvPolynomial.algebraMap_eq]
      ring
    rw [key, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  · rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem rowAct_diagonal {r c : ℕ} (d : Fin r → ℂ) :
    rowAct ℂ (n := c) (Matrix.diagonal d) = aeval (fun v : Fin r × Fin c => C (d v.1) * X v) := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  congr 1
  funext v
  rw [Finset.sum_eq_single v.1]
  · simp
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
  · simp

theorem prod_rowDeg {r c : ℕ} (x : Fin r → ℂ) (m : Fin r × Fin c →₀ ℕ) :
    (m.prod fun v k => x v.1 ^ k) = ∏ a, x a ^ rowDeg m a := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  unfold rowDeg
  show ∏ y : Fin c, x a ^ m (a, y) = x a ^ ∑ s, m (a, s)
  rw [Finset.prod_pow_eq_pow_sum]

theorem coeff_sqAct_diag {r : ℕ} (lam : DomWeight r) (t : Fin r → ℂˣ) (f : MvPolynomial (Fin r × Fin r) ℂ)
    (m : Fin r × Fin r →₀ ℕ) :
    AddMonoidAlgebra.coeff (sqAct ℂ r lam (diagGL ℂ r t) f) m =
      (∏ a, (t a : ℂ)) ^ lam.detShift * ((∏ a, (t a : ℂ) ^ rowDeg m a) * AddMonoidAlgebra.coeff f m) := by
  have hdet : detPow ℂ r (diagGL ℂ r t) lam.detShift = (∏ a, (t a : ℂ)) ^ lam.detShift := by
    unfold detPow
    rw [Units.val_zpow_eq_zpow_val]
    congr 1
    show Matrix.det (Matrix.diagonal fun a => (t a : ℂ)) = _
    exact Matrix.det_diagonal
  have htr : ((diagGL ℂ r t : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).transpose =
      Matrix.diagonal fun a => (t a : ℂ) :=
    Matrix.diagonal_transpose _
  unfold sqAct
  rw [coeff_smul, smul_eq_mul, hdet, htr, rowAct_diagonal, coeff_aeval_scale,
    prod_rowDeg (fun a => (t a : ℂ)) m]

theorem weight_rowW_apply {r c : ℕ} (m : Fin r × Fin c →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r c) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  unfold rowDeg
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [rowW]
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    simp [rowW, Pi.single_apply, Ne.symm hb]
  · simp

theorem weight_colW_apply {r c : ℕ} (m : Fin r × Fin c →₀ ℕ) (j : Fin c) :
    Finsupp.weight (colW r c) m j = ∑ a, m (a, j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single j]
  · simp [colW]
  · intro b _ hb
    simp [colW, Pi.single_apply, Ne.symm hb]
  · simp

theorem weight_lastW {n : ℕ} (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) :
    Finsupp.weight (lastW (n + 1)) m = rowDeg m (Fin.last n) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  unfold rowDeg
  rw [Finset.sum_eq_single (Fin.last n)]
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp [lastW]
  · intro b _ hb
    refine Finset.sum_eq_zero fun s _ => ?_
    have hb' : ¬ (b.1 = n) := fun h => hb (Fin.ext (by simp [h]))
    simp [lastW, hb']
  · simp

theorem sum_rowDeg_of_mem {r : ℕ} (lam : DomWeight r) (f : MvPolynomial (Fin r × Fin r) ℂ)
    (hf : f ∈ nablaSq ℂ r lam) (m : Fin r × Fin r →₀ ℕ) (hm : AddMonoidAlgebra.coeff f m ≠ 0) :
    ∑ a, rowDeg m a = ∑ j, lam.natW j := by
  have hf' : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ r r lam.natW := hf
  have hw : Finsupp.weight (colW r r) m = lam.natW :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hf').1 hm
  calc ∑ a, rowDeg m a = ∑ a, ∑ j, m (a, j) := rfl
    _ = ∑ j, ∑ a, m (a, j) := Finset.sum_comm
    _ = ∑ j, Finsupp.weight (colW r r) m j := by simp only [weight_colW_apply]
    _ = ∑ j, lam.natW j := by rw [hw]

theorem sum_natW {r : ℕ} (lam : DomWeight r) :
    ((∑ j, lam.natW j : ℕ) : ℤ) = wsum lam - r * lam.detShift := by
  push_cast
  have h : ∀ j : Fin r, ((lam.natW j : ℕ) : ℤ) = lam.w j - lam.detShift := by
    intro j
    have hj := j.isLt
    have hle : lam.detShift ≤ lam.w j := by
      unfold DomWeight.detShift
      rw [dif_pos (by omega : 0 < r)]
      exact lam.anti (Fin.le_iff_val_le_val.mpr (by show j.1 ≤ r - 1; omega))
    unfold DomWeight.natW
    omega
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_sub_distrib]
  simp [wsum]

theorem two_zpow_inj {k l : ℤ} (e : (2 : ℂ) ^ k = (2 : ℂ) ^ l) : k = l := by
  have h : (((2 : ℝ) ^ k : ℝ) : ℂ) = (((2 : ℝ) ^ l : ℝ) : ℂ) := by
    push_cast
    exact e
  exact zpow_right_injective₀ (by norm_num) (by norm_num) (Complex.ofReal_injective h)

theorem embGL_diagGL {n : ℕ} (t : Fin n → ℂˣ) :
    embGL ℂ n (n + 1) rfl (diagGL ℂ n t) =
      diagGL ℂ (n + 1) (fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1) := by
  apply Units.ext
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [embGL, blkHom, diagGL, Matrix.diagonal_apply, Matrix.reindexAlgEquiv_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply, Fin.ext_iff] <;> omega

theorem coeff_eq_of_eqv {n : ℕ} (lam : DomWeight (n + 1)) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hφ : IsEqv rfl mu lam φ) (t : Fin n → ℂˣ) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu)
    (κ : ℂ) (hκ : sqAct ℂ n mu (diagGL ℂ n t) s = κ • s) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ)
    (hm : AddMonoidAlgebra.coeff (φ s) m ≠ 0) :
    (∏ i, (t i : ℂ)) ^ lam.detShift * ∏ i, (t i : ℂ) ^ rowDeg m (Fin.castSucc i) = κ := by
  have h1 := hφ.2 (diagGL ℂ n t) s hs
  rw [hκ, map_smul, embGL_diagGL] at h1
  have h2 := congrArg (AddMonoidAlgebra.coeff · m) h1
  rw [coeff_smul, coeff_sqAct_diag, smul_eq_mul, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc] at h2
  simp only [Fin.coe_castSucc, Fin.is_lt, dite_true, dif_pos, Fin.eta, Fin.val_last, lt_self_iff_false,
    dite_false, Units.val_one, one_pow, mul_one] at h2
  exact mul_right_cancel₀ hm (by linear_combination (-1 : ℂ) * h2)

theorem equivariant_last_degree_coeff {n : ℕ} (lam : DomWeight (n + 1)) (mu : DomWeight n)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hφ : IsEqv rfl mu lam φ) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu)
    (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ) (hm : AddMonoidAlgebra.coeff (φ s) m ≠ 0) :
    ((rowDeg m (Fin.last n) : ℕ) : ℤ) = wsum lam - wsum mu - lam.detShift := by
  set t : Fin n → ℂˣ := fun _ => Units.mk0 (2 : ℂ) two_ne_zero with ht
  have htv : ∀ i, (t i : ℂ) = 2 := fun _ => rfl
  have hκ : sqAct ℂ n mu (diagGL ℂ n t) s =
      ((∏ i : Fin n, (t i : ℂ)) ^ mu.detShift * (2 : ℂ) ^ (∑ j, mu.natW j)) • s := by
    ext m'
    rw [coeff_sqAct_diag, coeff_smul, smul_eq_mul]
    by_cases h0 : AddMonoidAlgebra.coeff s m' = 0
    · simp [h0]
    · have hs' := sum_rowDeg_of_mem mu s hs m' h0
      simp only [htv, Finset.prod_pow_eq_pow_sum, hs']
      ring
  have h1 := coeff_eq_of_eqv lam mu φ hφ t s hs _ hκ m hm
  simp only [htv, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum] at h1
  have hz : ∀ (a : ℕ) (d : ℤ), ((2 : ℂ) ^ a) ^ d = (2 : ℂ) ^ ((a : ℤ) * d) := by
    intro a d
    rw [← zpow_natCast, ← zpow_mul]
  have hn : ∀ a : ℕ, (2 : ℂ) ^ a = (2 : ℂ) ^ (a : ℤ) := fun a => (zpow_natCast 2 a).symm
  rw [hz, hz, hn (∑ i : Fin n, rowDeg m (Fin.castSucc i)), hn (∑ j, mu.natW j),
    ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0), ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0)] at h1
  have E := two_zpow_inj h1
  have hmem : φ s ∈ nablaSq ℂ (n + 1) lam := hφ.1 s hs
  have T := sum_rowDeg_of_mem lam (φ s) hmem m hm
  rw [Fin.sum_univ_castSucc] at T
  have SL := sum_natW lam
  have SM := sum_natW mu
  have T' : ((∑ i : Fin n, rowDeg m (Fin.castSucc i) : ℕ) : ℤ) + (rowDeg m (Fin.last n) : ℤ) =
      ((∑ j, lam.natW j : ℕ) : ℤ) := by exact_mod_cast T
  push_cast at E SL SM T' ⊢
  linear_combination (-1 : ℤ) * E + T' + SL - SM

end EqvWt

open EqvWt in
theorem equivariant_last_degree : EqvLast := by
  intro n N h lam mu _ φ hφ s hs
  subst h
  intro m hm
  rw [weight_lastW]
  have := equivariant_last_degree_coeff lam mu φ hφ s hs m hm
  show rowDeg m (Fin.last n) = (wsum lam - wsum mu - lam.detShift).toNat
  omega

open EqvWt in
theorem equivariant_partial_weight : EqvRowWt := by
  intro n N h lam mu hI φ hφ ω s hs hω
  subst h
  intro m hm
  funext a
  rw [weight_rowW_apply]
  induction a using Fin.lastCases with
  | last =>
    have := equivariant_last_degree_coeff lam mu φ hφ s hs m hm
    unfold liftWt
    rw [dite_eq_right (by simp)]
    show rowDeg m (Fin.last n) = (wsum lam - wsum mu - lam.detShift).toNat
    omega
  | cast i =>
    have hi := i.isLt
    let t : Fin n → ℂˣ := fun j => if j = i then Units.mk0 (2 : ℂ) two_ne_zero else 1
    have hp : ∀ f : Fin n → ℕ, ∏ j, (t j : ℂ) ^ f j = 2 ^ f i := by
      intro f
      rw [Finset.prod_eq_single i]
      · simp [t]
      · intro j _ hj
        simp [t, hj]
      · simp
    have hp0 : ∏ j, (t j : ℂ) = 2 := by simpa using hp (fun _ => 1)
    have hκ : sqAct ℂ n mu (diagGL ℂ n t) s =
        ((∏ j, (t j : ℂ)) ^ mu.detShift * ∏ j, (t j : ℂ) ^ ω j) • s := by
      ext m'
      rw [coeff_sqAct_diag, coeff_smul, smul_eq_mul]
      by_cases h0 : AddMonoidAlgebra.coeff s m' = 0
      · simp [h0]
      · have hw := hω h0
        have hr : ∀ j, rowDeg m' j = ω j := fun j => by rw [← weight_rowW_apply, hw]
        simp only [hr]
        ring
    have h1 := coeff_eq_of_eqv lam mu φ hφ t s hs _ hκ m hm
    rw [hp0, hp (fun j => rowDeg m (Fin.castSucc j)), hp ω] at h1
    rw [← zpow_natCast, ← zpow_natCast (2 : ℂ) (ω i), ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0),
      ← zpow_add₀ (two_ne_zero : (2 : ℂ) ≠ 0)] at h1
    have E := two_zpow_inj h1
    have hle : lam.detShift ≤ mu.detShift := by
      have h2 := (hI ⟨n - 1, by omega⟩).2
      unfold DomWeight.detShift
      rw [dif_pos (by omega : 0 < n + 1), dif_pos (by omega : 0 < n)]
      exact (le_of_eq (congrArg lam.w (Fin.ext (by show n + 1 - 1 = n - 1 + 1; omega)))).trans h2
    unfold liftWt
    rw [dif_pos (by simp)]
    simp only [Fin.coe_castSucc, Fin.eta]
    omega

end PI.WGL
end
end

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem liftMod_of (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hZ : CapelliZ) (hV : ZScalarVanish)
    (hN : Numbers) (hX : XiFacts) : LiftMod :=
  liftMod_asm hZ hV hN hX equivariant_divisibility equivariant_partial_weight (decomp_of h4 equivariant_last_degree)
    (zComm_of h4 equivariant_divisibility equivariant_partial_weight) (fockDetect_of h3 equivariant_divisibility) tuple_decomposition_formula

end PI.WGL
