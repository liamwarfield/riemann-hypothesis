module

public import ReciprocityTheory.DualLattices.SubMemOfCompat

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.StdJForm4
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

theorem btP_facts (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (π : Equiv.Perm (Fin m)) (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hσ : ∀ i, σ (e i) = e (π i)) (hsT : (∑ i, H.ρ (e i)) + H.P = 1)
    (hPT : ∀ i, H.ρ (e i) * H.P = 0) (hsL : (∑ i, H.ρL (e i)) + H.PL = 1)
    (hPL : ∀ i, H.ρL (e i) * H.PL = 0) :
    (btP H e)ᵀ * H.Ht - H.Htᵀ * btP H e = cp • H.E.map (algebraMap ℤ_[p] R) ∧
    (∀ i, btP H e * (H.ρ (e i)).map (algebraMap ℤ_[p] R) = H.ρL (e i) * btP H e) ∧
    btP H e * H.P.map (algebraMap ℤ_[p] R) = H.PL * btP H e := by
  classical
  set F := (algebraMap ℤ_[p] R).mapMatrix (m := Ix g) with hF
  have hFa : ∀ M : Matrix (Ix g) (Ix g) ℤ_[p], M.map (algebraMap ℤ_[p] R) = F M := fun M => rfl
  have hFt : ∀ M : Matrix (Ix g) (Ix g) ℤ_[p], (F M)ᵀ = F Mᵀ := fun M => rfl
  let π2 := pi2 e π hσ
  have hπ2 : ∀ k, π2 (π2 k) = k := involutionPerm_involutive e π hσ horth hS.invol
  let εT : Fin (m + 1) → Matrix (Ix g) (Ix g) R :=
    Fin.lastCases (F H.P) (fun i => F (H.ρ (e i)))
  let εL : Fin (m + 1) → Matrix (Fin g) (Fin g) R :=
    Fin.lastCases H.PL (fun i => H.ρL (e i))
  let π' : Equiv.Perm (Fin (m + 1)) := finSuccEquivLast.symm.permCongr (Equiv.optionCongr π2)
  have hTc : ∀ i : Fin m, εT i.castSucc = F (H.ρ (e i)) := fun i => by simp [εT]
  have hTl : εT (Fin.last m) = F H.P := by simp [εT]
  have hLc : ∀ i : Fin m, εL i.castSucc = H.ρL (e i) := fun i => by simp [εL]
  have hLl : εL (Fin.last m) = H.PL := by simp [εL]
  have hπc : ∀ i : Fin m, π' i.castSucc = (π2 i).castSucc := fun i => by
    simp [π', Equiv.permCongr_apply]
  have hπl : π' (Fin.last m) = Fin.last m := by simp [π', Equiv.permCongr_apply]
  have hPρ : ∀ i, H.P * H.ρ (e i) = 0 := fun i => by rw [H.projectors.2.2.2.1, hPT]
  have hPLρ : ∀ i, H.PL * H.ρL (e i) = 0 := fun i => by rw [H.projectors.2.2.2.2, hPL]
  have h1 : ∀ i, π' (π' i) = i := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hπl, hπl]
    · rw [hπc, hπc, hπ2]
  have h2 : ∀ i j, εT i * εT j = if i = j then εT i else 0 := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [hTl, ← map_mul, H.projectors.1, if_pos rfl]
    · rw [hTl, hTc, ← map_mul, hPρ, map_zero, if_neg (Fin.castSucc_lt_last j).ne']
    · rw [hTl, hTc, ← map_mul, hPT, map_zero, if_neg (Fin.castSucc_lt_last i).ne]
    · rw [hTc, hTc, ← map_mul, ← map_mul, horth]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun h => hij (Fin.castSucc_injective _ h)), map_zero, map_zero]
  have h3 : ∑ i, εT i = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [hTc, hTl]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum F (fun i => H.ρ (e i)), ← map_add (f := _), hsT, map_one]
  have h4 : ∀ i j, εL i * εL j = if i = j then εL i else 0 := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [hLl, H.projectors.2.1, if_pos rfl]
    · rw [hLl, hLc, hPLρ, if_neg (Fin.castSucc_lt_last j).ne']
    · rw [hLl, hLc, hPL, if_neg (Fin.castSucc_lt_last i).ne]
    · rw [hLc, hLc, ← map_mul, horth]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun h => hij (Fin.castSucc_injective _ h)), map_zero]
  have h5 : ∑ i, εL i = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [hLc, hLl]
    exact hsL
  have h6 : ∀ i, H.Ht * εT i = (εL (π' i))ᵀ * H.Ht := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hTl, hπl, hLl, ← hFa, H.Ht_equivariant.2]
    · rw [hTc, hπc, hLc, ← hFa, H.Ht_equivariant.1, involutionPerm_sigma e π hσ i]
  have h7 : ∀ i, (εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) =
      H.E.map (algebraMap ℤ_[p] R) * εT (π' i) := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hTl, hπl, hTl, hFa, hFt, ← map_mul, ← map_mul, H.projectors.2.2.1]
    · rw [hTc, hπc, hTc, hFa, hFt, ← map_mul, ← map_mul, H.E_equivariant, involutionPerm_sigma e π hσ i]
  have hu := u1 R g (m + 1) H.Ht H.Bt (H.E.map (algebraMap ℤ_[p] R)) cp εT εL π' h1 h2 h3 h4 h5
    h6 h7 H.form_eq_alt
  have hB : (∑ i, εL i * H.Bt * εT i) = btP H e := by
    rw [Fin.sum_univ_castSucc]
    simp only [hLc, hLl, hTc, hTl, btP, hFa]
  obtain ⟨hA, hC, -⟩ := hu
  rw [hB] at hA hC
  refine ⟨hA, fun i => ?_, ?_⟩
  · have := hC i.castSucc
    rw [hTc, hLc, ← hFa] at this
    exact this
  · have := hC (Fin.last m)
    rw [hTl, hLl, ← hFa] at this
    exact this

private lemma stdJ_form4 {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.mul_apply, stdJ, Fintype.sum_sum_type, Matrix.one_apply] <;> ring

theorem phiP_J (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (π : Equiv.Perm (Fin m)) (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hσ : ∀ i, σ (e i) = e (π i)) (hsT : (∑ i, H.ρ (e i)) + H.P = 1)
    (hPT : ∀ i, H.ρ (e i) * H.P = 0) (hsL : (∑ i, H.ρL (e i)) + H.PL = 1)
    (hPL : ∀ i, H.ρL (e i) * H.PL = 0) :
    (phiP H e)ᵀ * stdJ R g * phiP H e = cp • H.E.map (algebraMap ℤ_[p] R) := by
  obtain ⟨h1, -, -⟩ := btP_facts hS H e π horth hσ hsT hPT hsL hPL
  ext i j
  rw [stdJ_form4, ← h1, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_sub_distrib]
  rfl

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.SurjectiveAinfTowerZero
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)

theorem surjective_ainfTower_zero : Function.Surjective ((ainfTowerL p O hv ε hε).q 0).1 :=
  fun y => Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O) ^ (0 + 1)}) y

theorem ker_ainfTower_zero : RingHom.ker ((ainfTowerL p O hv ε hε).q 0).1 =
    Ideal.span {((p : ℕ) : ((ainfTowerL p O hv ε hε).O : Type))} := by
  ext a
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  have hq : ((ainfTowerL p O hv ε hε).q 0).1 a =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ (0 + 1)}) a := rfl
  rw [hq]
  exact (Ideal.Quotient.eq_zero_iff_dvd _ _).trans (by rw [pow_one]; rfl)

theorem ainf_zeta0 (h2 : p = 2) :
    (((ainfTowerL p O hv ε hε).ζ 0 : ((ainfTowerL p O hv ε hε).O : Type)ˣ) :
      ((ainfTowerL p O hv ε hε).O : Type)) = -1 := by
  have hz : (((ainfTowerL p O hv ε hε).ζ 0 : ((ainfTowerL p O hv ε hε).O : Type)ˣ) :
      ((ainfTowerL p O hv ε hε).O : Type)) = ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt := by
    show zetaV p O ε 0 = _
    simp [zetaV, root, fontaineTheta_teichmuller]
  rw [hz]
  clear hz
  haveI : NoZeroDivisors O :=
    hv.hom_inj.noZeroDivisors _ (map_zero _) (map_mul _)
  set z := ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt with hzdef
  clear_value z
  rw [h2] at hε
  exact hε.eq_neg_one_of_two_right

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.HtdOf
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def Dat.hopf (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] [Algebra (Tw.O : Type) C]
    (hdom : IsDomain (Tw.O : Type)) (hinj : Function.Injective (algebraMap (Tw.O : Type) C))
    (hLat : EvLatStatement D) (hHopf : EvHopfStatement D) : HopfOrder (C := C) (Tw.O : Type) (Nb p g) where
  carrier := D.evImg C
  lat := (hLat C hdom hinj).1
  le_int := (hLat C hdom hinj).2.1
  one_mem := (hLat C hdom hinj).2.2.1
  mul_mem := (hLat C hdom hinj).2.2.2
  comul := (hHopf C hinj).1
  antipode := (hHopf C hinj).2

def htd_of (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] (v : Valuation C NNReal)
    [Algebra (Tw.O : Type) C] (hdom : IsDomain (Tw.O : Type))
    (hinj : Function.Injective (algebraMap (Tw.O : Type) C))
    (hLat : EvLatStatement D) (hHopf : EvHopfStatement D) (hAct : EvActStatement D)
    (hHt : EvHtStatement D) (hBt : EvBtStatement D) (hH5 : EvenTwoEvaluationSign D) (hCot : EvCotStatement D) :
    HodgeTateDatum p g v (Tw.O : Type) Oe σ cp where
  ρ := D.H.ρ
  ρL := D.H.ρL
  P := D.H.P
  PL := D.H.PL
  E := D.H.E
  E_alternating := D.H.E_alternating
  isUnit_det_E := D.H.isUnit_det_E
  E_equivariant := D.H.E_equivariant
  projectors := D.H.projectors
  Ht := D.H.Ht
  Bt := D.H.Bt
  Ht_equivariant := D.H.Ht_equivariant
  form_eq_alt := D.H.form_eq_alt
  AA := D.hopf C hdom hinj hLat hHopf
  h3 := fun a f hf => hAct C a f hf
  h4 := fun k => ⟨hHt C k, hBt C k⟩
  h5 := fun hp2 s => hH5 C hdom hinj hp2 s
  φ := Classical.choose (hCot C hinj)
  cotangent_surjective := (Classical.choose_spec (hCot C hinj)).1
  cotangent_ker_eq := (Classical.choose_spec (hCot C hinj)).2.1
  cotangent_linear := (Classical.choose_spec (hCot C hinj)).2.2

end ReciprocityTheory.PGsh.Be2
end
end
