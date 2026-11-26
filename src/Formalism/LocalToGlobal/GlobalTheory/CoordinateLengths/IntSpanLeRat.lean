module

public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchOfCoordinatesAndCount
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PKerAtP
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocInd

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchCoordinatesOfSurjectivity
section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.ValuationDetBasisChangeZero
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB.V0

open Formalism.BasicNotions NumberField Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Classical Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open scoped Matrix

variable (D : D7) (u : D.what₂.Word)

theorem residue_nat_ne_zero_level_zero (Tt : Forms0 D u) (v : (D.mem u).A.vT) (s : ℕ) (hs : ¬ (D.mem u).A.T ∣ s) :
    Tt.atT.res v (s : 𝓞 D.host.E) ≠ 0 := by
  haveI : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  intro h
  apply hs
  rw [map_natCast] at h
  have e : (D.mem u).A.Fv v ≃+* ZMod (D.mem u).A.T :=
    FiniteField.ringEquivOfCardEq (by rw [(D.mem u).A.card_Fv v, ZMod.card])
  have h2 : (s : ZMod (D.mem u).A.T) = 0 := by
    rw [← map_natCast e s, h, map_zero]
  exact (CharP.cast_eq_zero_iff (ZMod (D.mem u).A.T) (D.mem u).A.T s).mp h2

theorem not_T_dvd_finset_prod {ι : Type} (s : Finset ι) (f : ι → ℕ) (h : ∀ i ∈ s, ¬ (D.mem u).A.T ∣ f i) :
    ¬ (D.mem u).A.T ∣ ∏ i ∈ s, f i := by
  exact not_dvd_prod_of_not_dvd (D := D) (u := u) s f h

theorem det_basis_change_mem_prime_zero (Tt : Forms0 D u) (w : D.what₂.places.Pl) (hw : OverT D u w) (v : (D.mem u).A.vT)
    (i : ℕ) (hi : i ≤ D.R.m) (h0 : i = 0) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B') :
    ∃ (S : ℕ) (x : 𝓞 D.host.E), ¬ (D.mem u).A.T ∣ S ∧ Tt.atT.res v x = 0 ∧
      (x : D.host.E) = (S : D.host.E) ^ D.R.N i *
        (((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).det := by
  set M : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E := ((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) with hMdef
  have hLk : Lk Tt.atT i hi v c ≤ Ld D u i hi c := sup_le (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.bwL_lcInt0 D u Tt i hi h0 c) Submodule.smul_le_right
  have hone : ¬ (D.mem u).A.T ∣ 1 := (D.mem u).A.T_prime.not_dvd_one

  choose sk hsk hskL using fun k => bwD_col_loc D u w hw hB' k
  have hcolM : ∀ k a, (((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ
      (fun r => (B' : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r k)) a = M a k := by
    intro k a; rw [bwD_mulVec_col, ← Units.val_mul]
  have hco : ∀ k, ∃ s' : ℕ, ¬ (D.mem u).A.T ∣ s' ∧ ∀ a, ((s' * sk k : ℕ) : D.host.E) * M a k ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro k
    obtain ⟨s', hs', hm⟩ := (hB ((sk k : D.host.E) • fun r => (B' : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r k)).1
      ⟨1, hone, by rw [Nat.cast_one, one_smul]; exact hLk (hskL k)⟩
    refine ⟨s', hs', fun a => ?_⟩
    have := hm a
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hcolM] at this
    rw [Nat.cast_mul, mul_assoc]; exact this
  choose s2 hs2 hs2m using hco
  set S : ℕ := ∏ k, s2 k * sk k with hSdef
  have hS : ¬ (D.mem u).A.T ∣ S :=
    not_T_dvd_finset_prod D u _ _ (fun k _ => by
      intro hd
      rcases (Nat.Prime.dvd_mul (D.mem u).A.T_prime).1 hd with h | h
      · exact hs2 k h
      · exact hsk k h)
  have hSM : ∀ a k, (S : D.host.E) * M a k ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro a k
    obtain ⟨q, hq⟩ : s2 k * sk k ∣ S := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
    rw [hq, Nat.cast_mul, mul_comm ((s2 k * sk k : ℕ) : D.host.E), mul_assoc]
    exact Subring.mul_mem _ ⟨(q : 𝓞 D.host.E), map_natCast _ _⟩ (hs2m k a)
  choose m hm using hSM

  choose tb htb htbL using fun a => bwD_col_loc D u w hw hB a
  set t : ℕ := ∏ a, tb a with htdef
  have ht : ¬ (D.mem u).A.T ∣ t := not_T_dvd_finset_prod D u _ _ (fun a _ => htb a)
  have hbL : ∀ a, (t : D.host.E) • (fun r => (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r a) ∈ (Ld D u i hi c : Set _) := by
    intro a
    obtain ⟨q, hq⟩ : tb a ∣ t := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
    have h1 := (Ld D u i hi c).smul_mem (q : 𝓞 D.host.E) (htbL a)
    have e : (q : 𝓞 D.host.E) • ((tb a : D.host.E) • fun r => (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r a) =
        (t : D.host.E) • fun r => (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r a := by
      ext r
      rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hq, Nat.cast_mul, Algebra.smul_def,
        map_natCast]
      ring
    rw [← e]; exact h1
  set eb : Fin (D.R.N i) → ↥(Ld D u i hi c) := fun a => ⟨_, hbL a⟩ with hebdef
  set P := Tt.lv i hi h0
  set φ : Fin (D.R.N i) → (D.mem u).A.Fv v := fun a => (D.fm u).fv i v c (P.pr v c (eb a)) with hφdef

  have hexp : ∀ (z : Fin (D.R.N i) → D.host.E) (g : Fin (D.R.N i) → 𝓞 D.host.E) (s : ℕ),
      (∀ a, (algebraMap (𝓞 D.host.E) D.host.E (g a)) = (s : D.host.E) * (((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ z) a) →
      ((s * t : ℕ) : D.host.E) • z = ∑ a, (algebraMap (𝓞 D.host.E) D.host.E (g a)) • ((eb a : ↥(Ld D u i hi c)) : Fin (D.R.N i) → D.host.E) := by
    intro z g s hg
    set cz := ((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ z with hcz
    have hz : z = (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ cz := by
      rw [hcz, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    ext r
    simp only [hebdef, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, hg, Nat.cast_mul]
    have hzr : z r = ∑ x, (B : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r x * cz x := by
      conv_lhs => rw [hz]
      rfl
    rw [hzr, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  have hprS : ∀ (z : ↥(Ld D u i hi c)) (g : Fin (D.R.N i) → 𝓞 D.host.E) (s : ℕ),
      (∀ a, (algebraMap (𝓞 D.host.E) D.host.E (g a)) = (s : D.host.E) * (((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ z.1) a) →
      Tt.atT.res v ((s * t : ℕ) : 𝓞 D.host.E) * (D.fm u).fv i v c (P.pr v c z) = ∑ a, Tt.atT.res v (g a) * φ a := by
    intro z g s hg
    have hz : ((s * t : ℕ) : 𝓞 D.host.E) • z = ∑ a, g a • eb a := by
      apply Subtype.ext
      rw [Submodule.coe_smul, Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [show ((s * t : ℕ) : 𝓞 D.host.E) • z.1 = ((s * t : ℕ) : D.host.E) • z.1 by
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]]
      rw [hexp z.1 g s hg]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Algebra.smul_def]; rfl
    have := congrArg (fun y => (D.fm u).fv i v c (P.pr v c y)) hz
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P.pr_smul, map_smul, map_sum, smul_eq_mul] at this
    exact this

  have hφ : φ ≠ 0 := by
    intro h0
    apply (D.fm u).fv_ne i v c
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := P.pr_surj v c y
    obtain ⟨s3, hs3, hs3m⟩ := (hB z.1).1 ⟨1, hone, by rw [Nat.cast_one, one_smul]; exact z.2⟩
    choose g hg using hs3m
    have h := hprS z g s3 (fun a => hg a)
    simp only [h0, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
    rcases mul_eq_zero.1 h with h1 | h1
    · exact absurd h1 (residue_nat_ne_zero_level_zero D u Tt v _ (by
        intro hd
        rcases (Nat.Prime.dvd_mul (D.mem u).A.T_prime).1 hd with h | h
        · exact hs3 h
        · exact ht h))
    · rw [h1]; rfl

  have hrel : ∀ k, ∑ a, Tt.atT.res v (m a k) * φ a = 0 := by
    intro k
    have hg : ∀ a, algebraMap (𝓞 D.host.E) D.host.E ((sk k : 𝓞 D.host.E) * m a k) =
        (S : D.host.E) * (((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) *ᵥ
          ((sk k : D.host.E) • fun r => (B' : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) r k)) a := by
      intro a
      rw [map_mul, map_natCast, hm a k, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hcolM]; ring
    have h := hprS ⟨_, hLk (hskL k)⟩ (fun a => (sk k : 𝓞 D.host.E) * m a k) S hg
    rw [((P.fv_ker v c ⟨_, hLk (hskL k)⟩).2 (hskL k)), mul_zero] at h
    simp only [map_mul, mul_assoc] at h
    rw [← Finset.mul_sum] at h
    rcases mul_eq_zero.1 h.symm with h1 | h1
    · exact absurd h1 (residue_nat_ne_zero_level_zero D u Tt v _ (hsk k))
    · exact h1

  have hdetR : (Matrix.of fun a k => Tt.atT.res v (m a k)).det = 0 := by
    refine Matrix.exists_vecMul_eq_zero_iff.1 ⟨φ, hφ, funext fun k => ?_⟩
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
    rw [← hrel k]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine ⟨S, (Matrix.of m).det, hS, ?_, ?_⟩
  · rw [RingHom.map_det]; exact hdetR
  · show algebraMap (𝓞 D.host.E) D.host.E (Matrix.of m).det = _
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have e : (Matrix.of m).map (algebraMap (𝓞 D.host.E) D.host.E) = (S : D.host.E) • M := by
      ext a k; simp [hm a k]
    rw [e, Matrix.det_smul, Fintype.card_fin]

theorem withTop_add_neg_nonneg (a : WithTop ℤ) (e : ℤ) (h : (e : WithTop ℤ) ≤ a) : 0 ≤ a + -(e : WithTop ℤ) := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe b =>
    have hb : e ≤ b := by exact_mod_cast h
    have key : ((b : WithTop ℤ) + -(e : WithTop ℤ)) = ((b - e : ℤ) : WithTop ℤ) := by
      first
        | rw [sub_eq_add_neg, WithTop.coe_add, WithTop.LinearOrderedAddCommGroup.coe_neg]
        | norm_cast
        | simp [sub_eq_add_neg]
    rw [key]
    exact_mod_cast (show (0 : ℤ) ≤ b - e by omega)

theorem valuation_det_basis_change_zero (Tt : Forms0 D u) (hU : UnramifiedAtLevelPrimes D u Tt.atT) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (hs : (D.fm u).seenP w = true) (v : (D.mem u).A.vT)
    (i : ℕ) (hi : i ≤ D.R.m) (h0 : i = 0) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B') :
    ((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w := by
  obtain ⟨S, x, hS, hx0, hxe⟩ := det_basis_change_mem_prime_zero D u Tt w hw v i hi h0 c B B' hB hB'
  have hv := hU w hw hs v x hx0
  set σ := D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG) with hσ
  set δ := (((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).det with hδ
  have hS0 : D.what₂.places.val w (S : D.what₂.LL) = 0 :=
    bwA_val_nat_eq_zero D.what₂.places w S (by rw [hw]; exact hS)
  have hvx : D.what₂.places.val w (D.embE (σ (x : D.host.E))) = D.what₂.places.val w (D.embE (σ δ)) := by
    rw [hxe, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, AddValuation.map_mul, AddValuation.map_pow,
      hS0, nsmul_zero, zero_add]
  rw [hvx] at hv
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  refine Subring.mem_map.2 ⟨D.embE (σ δ) * ((D.mem u).A.T : D.what₂.LL)⁻¹, ?_, ?_⟩
  · show (0 : WithTop ℤ) ≤ D.what₂.places.val w (D.embE (σ δ) * ((D.mem u).A.T : D.what₂.LL)⁻¹)
    rw [AddValuation.map_mul, AddValuation.map_inv, ← hw, D.what₂.places.val_resChar]
    exact withTop_add_neg_nonneg _ _ hv
  · rw [map_mul, map_inv₀, map_natCast]
    change _ = (Forms.embT D _ _) * _
    rw [bwA_embT_eq]

theorem det_basis_change_unit_zero (Tt : Forms0 D u) (hU : UnramifiedAtLevelPrimes D u Tt.atT) (w : D.what₂.places.Pl) (hw : OverT D u w)
    (hs : (D.fm u).seenP w = true) (v : (D.mem u).A.vT)
    (i : ℕ) (hi : i ≤ D.R.m) (h0 : i = 0) (c : (D.mem u).C.cls i) (B B' : GL (Fin (D.R.N i)) D.host.E)
    (hB : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B)
    (hB' : IsLocBasis (D.mem u).A.T (Lk Tt.atT i hi v c : Set _) B') :
    ((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det * (((D.mem u).A.T : ℂ))⁻¹ ∈ bwA_Ow D w ∧
    ((D.mem u).A.T : ℂ) * (((((B⁻¹ * B' : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)).map
        (embT D ((D.fm u).tauOf w v))).det)⁻¹ ∈ bwA_Ow D w :=
  ⟨valuation_det_basis_change_zero D u Tt hU w hw hs v i hi h0 c B B' hB hB',
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.basis_change_mem_elementary (D := D) (u := u) Tt w hw v ((D.fm u).tauOf w v) i hi h0 c B B' hB hB').2.2.2⟩

end Formalism.L2.GlobalTheoryTheory.LemB.V0
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB NumberField Classical

theorem locBases {D : D7} {u : D.what₂.Word} (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    (∃ B : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B) ∧
    ∀ v, ∃ B' : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Lk A i hi v c : Set _) B' := by
  have : Fact (D.mem u).A.T.Prime := ⟨(D.mem u).A.T_prime⟩
  have hL := bwB_clsCrd_lat D u i hi c
  have hFull : Submodule.IsFullLattice D.host.E (clsCrd D u i hi c) :=
    { toIsLattice := hL, span_eq_top := (tld_isLat i hi c).2 }
  obtain ⟨d, hd, hle⟩ := dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (bwB_gramN_det D i hi) _ hFull
  obtain ⟨d0, hd0, hle0⟩ := exists_le_bnd _ hL
  have hLd : Ld D u i hi c ≤ bnd d := hle
  have hLd_sp := dual_span (sigD D : D.host.E →+* D.host.E) (gramN D i hi) _ hL
  refine ⟨exists_isLocBasis _ _ _ (fg_of_le_bnd hd hLd) hLd_sp, fun v => exists_isLocBasis _ _ _ ?_ ?_⟩
  · refine fg_of_le_bnd (mul_ne_zero hd hd0) (sup_le (hle0.trans (bnd_mono d0 d)) ?_)
    refine (Submodule.smul_le_right.trans hLd).trans ?_
    rw [mul_comm]
    exact bnd_mono d d0
  · apply eq_top_iff.2
    rw [← hLd_sp]
    apply Submodule.span_le.2
    intro z hz
    have ht : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast (D.mem u).A.T_prime.ne_zero
    have hm : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ A.Pv v := by
      show A.res v _ = 0
      rw [map_natCast, ← (D.mem u).A.card_Fv v]
      exact FiniteField.cast_card_eq_zero _
    have hz' : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z ∈ Lk A i hi v c :=
      Submodule.mem_sup_right (Submodule.smul_mem_smul hm hz)
    have h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z ∈
        Submodule.span D.host.E (Lk A i hi v c : Set _) := Submodule.subset_span hz'
    have hfield : (((D.mem u).A.T : ℕ) : D.host.E) • z ∈
        Submodule.span D.host.E (Lk A i hi v c : Set _) := by
      change (algebraMap (𝓞 D.host.E) D.host.E (((D.mem u).A.T : ℕ) : 𝓞 D.host.E)) • z ∈ _
      rw [IsScalarTower.algebraMap_smul]
      exact h
    have h' := (Submodule.span D.host.E (Lk A i hi v c : Set (Fin (D.R.N i) → D.host.E))).smul_mem
      ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹) hfield
    simpa [smul_smul, ht] using h'

def OntoAll (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ T : Forms0 D u, admS D u → ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
    ∀ B B' : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E,
      (∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) →
      (∀ c, IsLocBasis (D.mem u).A.T (Lk T.atT 0 (Nat.zero_le _) v c : Set _) (B' c)) →
      OntoAt T w v B B'

theorem second_branch_coordinates_of_surjectivity {D : D7} {u : D.what₂.Word} (h : OntoAll D u) : SecondBranchCoordinates D u := by
  intro T hA w hw hs v hb
  choose B hB using fun c => (locBases T.atT 0 (Nat.zero_le _) c).1
  choose B' hB' using fun c => (locBases T.atT 0 (Nat.zero_le _) c).2 v
  refine ⟨B, B', hB, hB', fun c => ?_, h T hA w hw hs v hb B B' hB hB'⟩
  exact V0.det_basis_change_unit_zero D u T (Formalism.L2.Host.second_unramified_condition_holds (D := D) (u := u) T.atT) w hw hs v 0 (Nat.zero_le _) rfl c
    (B c) (B' c) (hB c) (hB' c)

theorem second_branch_of_surjectivity (hO : ∀ (D : D7) (u : D.what₂.Word), OntoAll D u)
    (hd : ∀ (D : D7) (u : D.what₂.Word), Forms0 D u → admS D u → DuCount D u) :
    ∀ (D : D7) (u : D.what₂.Word), Formalism.MainNotions.RT.SecondBranchIntegralityUnderForms D u :=
  second_branch_of_coordinates_and_count (fun D u => second_branch_coordinates_of_surjectivity (hO D u)) hd

end Formalism.L2.GlobalTheoryTheory.LemB
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.LocalGlobalOfBasisIndependence
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB.G0

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField Classical Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open scoped Matrix

variable (D : D7) (u : D.what₂.Word)

def BwLocGlob0 (Tt : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → ∀ i (hi : i ≤ D.R.m) (h0 : i = 0) (y : ((D.fm u).lat i).V),
    (∀ c, ∃ B : GL (Fin (D.R.N i)) D.host.E, IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B ∧
      ∃ Q ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i), ∀ z, (D.fm u).emb i y c z =
        fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q ((Tt.val i hi h0).eY z)) →
    y ∈ (D.fm u).S i w

def BwBasisInd0 (Tt : Forms0 D u) : Prop :=
  ∀ w, OverT D u w → ∀ i (hi : i ≤ D.R.m) (h0 : i = 0) (c : (D.mem u).C.cls i) (B B₂ : GL (Fin (D.R.N i)) D.host.E),
    IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B → IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B₂ →
    ∀ Q ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i), ∃ Q₂ ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam i), ∀ z,
      fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q ((Tt.val i hi h0).eY z) =
        fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B₂⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) Q₂ ((Tt.val i hi h0).eY z)

theorem local_global_of_basis_independence (Tt : Forms0 D u) (hI : BwBasisInd0 D u Tt) : BwLocGlob0 D u Tt := by
  intro w hw i hi h0 y hy
  show y ∈ locW D.what₂.places w ((D.fm u).lat i).L
  rw [D.mem_locW_iff]
  obtain ⟨-, -, hsp⟩ := (D.fm u).lat_good i
  obtain ⟨d, hd, hdy⟩ := Formalism.L2.DIV.lc_exists_smul_mem ((D.fm u).lat i).L (x := y) (by rw [hsp]; trivial)
  obtain ⟨t, ht, htw⟩ := Formalism.L2.DIV.lc_primeTo d hd (D.plEq w)
  refine ⟨t, ht, ?_⟩
  refine ((Tt.val i hi h0).lat _).2 fun w' c B hB => ?_
  by_cases hw' : w' = w
  · subst hw'
    obtain ⟨B₀, hB₀, Q, hQ, hyQ⟩ := hy c
    have hB' : IsLocBasis (D.mem u).A.T (Ld D u i hi c : Set _) B := by
      rw [bwG_Ld_coe, ← hw]
      exact hB
    obtain ⟨Q₂, hQ₂, he⟩ := hI w' hw i hi h0 c B₀ B hB₀ hB' Q hQ
    refine ⟨_, bwG_intSpan_smul D w' _ _ (bwG_int_mem D w' t) hQ₂, fun z => ?_⟩
    rw [← algebraMap_smul D.what₂.LL t y, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hyQ z, he z,
      LinearMap.map_smul]
    rfl
  · have hne : D.plEq w' ≠ D.plEq w := fun h => hw' (D.plEq.injective h)
    obtain ⟨r, hr, k, hk⟩ := htw _ hne
    obtain ⟨P, hP, hdP⟩ := ((Tt.val i hi h0).lat _).1 hdy w' c B hB
    have hr0 : algebraMap (𝓞 D.what₂.LL) D.what₂.LL r ≠ 0 := by
      intro h
      apply hr
      have : r = 0 := FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL (by rw [h, map_zero])
      rw [this]
      exact zero_mem _
    have e : t • y = ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL r)⁻¹ * algebraMap (𝓞 D.what₂.LL) D.what₂.LL k) • (d • y) := by
      rw [← algebraMap_smul D.what₂.LL t y, ← algebraMap_smul D.what₂.LL d y, smul_smul]
      congr 1
      have hk' := congrArg (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) hk
      rw [map_mul, map_mul] at hk'
      field_simp
      rw [mul_comm, hk', mul_comm]
    refine ⟨_, bwG_intSpan_smul D w' _ _ (mul_mem (bwG_inv_mem D w' hr) (bwG_int_mem D w' k)) hP, fun z => ?_⟩
    rw [e, LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, hdP z, LinearMap.map_smul]
    rfl

theorem bwBasisInd_of_stab0 (Tt : Forms0 D u) (hS : ∀ w, OverT D u w → BwGLStab D w) : BwBasisInd0 D u Tt := by
  intro w hw i hi h0 c B B₂ hB hB₂ Q hQ
  set N : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ :=
    fun τ => atInf (embT D) ((B⁻¹ * B₂ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ
    with hN
  set N' : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ :=
    fun τ => atInf (embT D) ((B₂⁻¹ * B : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ
    with hN'
  have hNN' : ∀ τ, N τ * N' τ = 1 := fun τ => by
    simp only [hN, hN', atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    have : (B⁻¹ * B₂ * (B₂⁻¹ * B) : GL (Fin (D.R.N i)) D.host.E) = 1 := by group
    rw [this, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ shiftOf (lamT u i) τ) * subP N Q,
    bwG_intSpan_allSubP D w _ N _ (fun τ g hg => hS w hw _ _ _ (N τ) (N' τ) (hNN' τ)
      (bwG_change_mem D u w hw τ hB₂ hB) (bwG_change_mem D u w hw τ hB hB₂) g hg) Q hQ, fun z => ?_⟩
  rw [← fnOf_mul]
  have hM : atInf (embT D) ((B⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) =
      fun τ => N τ * atInf (embT D) ((B₂⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ := by
    funext τ
    simp only [hN, atInf]
    rw [← Matrix.map_mul, ← Units.val_mul]
    congr 2
    group
  rw [hM]

theorem local_global_lattice_level_zero (Tt : Forms0 D u) : BwLocGlob0 D u Tt :=
  local_global_of_basis_independence D u Tt (bwBasisInd_of_stab0 D u Tt fun w _ => local_GL_stabilises_lattice D w)

end Formalism.L2.GlobalTheoryTheory.LemB.G0
end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable {D : D7} {u : D.what₂.Word}

def RatInC (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ P ∈ RatSpan D ((D.fm u).lam 0), P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam 0)

def RatGL (D : D7) (u : D.what₂.Word) : Prop :=
  ∀ (γ : D.what₂.Tau → GL (Fin (D.R.N 0)) D.host.E), ∀ P ∈ RatSpan D ((D.fm u).lam 0),
    MvPolynomial.C (∏ τ, (atInf (embT D) ((γ τ : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^ shiftOf (lamT u 0) τ) *
      subP (fun τ => atInf (embT D) ((γ τ : GL (Fin (D.R.N 0)) D.host.E) :
        Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) P ∈ RatSpan D ((D.fm u).lam 0)

theorem intSpan_le_rat (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N) :
    Formalism.L2.Forms.IntSpan D w lam ≤ RatSpan D lam := by
  apply AddSubgroup.closure_mono
  rintro p ⟨r, f, -, hf, rfl⟩
  exact ⟨r, f, hf, rfl⟩

theorem mem_intSubm (w : D.what₂.places.Pl) {N : ℕ} (lam : D.what₂.Tau → DomWeight N)
    (p : MvPolynomial (D.what₂.Tau × Fin N × Fin N) ℂ) : p ∈ intSubm D w lam → p ∈ Formalism.L2.Forms.IntSpan D w lam := by
  intro hp
  induction hp using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact (Formalism.L2.Forms.IntSpan D w lam).zero_mem
  | add x y _ _ hx hy => exact (Formalism.L2.Forms.IntSpan D w lam).add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨r, hr, hra⟩ := Subring.mem_map.mp a.2
    have ha : a • x = D.what₂.embLL r • x := by
      rw [Subring.smul_def, hra]
    rw [ha]
    exact Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwG_intSpan_smul (D := D) w lam r hr hx

theorem crd_surj (T : Forms0 D u) (hA : admS D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (Q : (D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ)
    (hQ : ∀ c, ∃ P ∈ RatSpan D ((D.fm u).lam 0), P ∈ Formalism.L2.Forms.CSpan ((D.fm u).lam 0) ∧
      ∀ y, fnOf (gramC (gramN D 0 (Nat.zero_le _)) (Forms.embT D)) (shiftOf (lamT u 0)) 1 P y =
        fnOf (gramC (gramN D 0 (Nat.zero_le _)) (Forms.embT D)) (shiftOf (lamT u 0))
          (atInf (Forms.embT D) ((B c)⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) (Q c) y) :
    ∃ x : ((D.fm u).lat 0).V, ∀ c, IsCrd T (B c) x c (Q c) := by
  let φ : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ := fun c z =>
    fnOf (gramC (gramN D 0 (Nat.zero_le _)) (Forms.embT D)) (shiftOf (lamT u 0))
      (atInf (Forms.embT D) ((B c)⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) (Q c) (T.val0.eY z)
  have hFi : φ ∈ (D.fm u).Fi 0 := by
    rw [(D.fm u).Fi_zero, S0.mem_forms_level_zero_iff T hA φ]
    intro c
    obtain ⟨P, -, hPC, hPe⟩ := hQ c
    refine ⟨P, hPC, ?_⟩
    funext y
    have e := hPe y
    rw [lamT_zero] at e
    simp only [φ, LinearMap.funLeft_apply]
    rw [lamT_zero, e]
    exact congrArg _ (T.val0.eY.apply_symm_apply y).symm
  obtain ⟨x, hx⟩ := (T.val0.rat φ).2 ⟨hFi, fun c => by
    obtain ⟨P, hPR, -, hPe⟩ := hQ c
    exact ⟨P, hPR, fun z => (hPe _).symm⟩⟩
  exact ⟨x, fun c z => by rw [hx]⟩

theorem fnOf_frame (B : GL (Fin (D.R.N 0)) D.host.E)
    (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) (y) :
    fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) 1
        (MvPolynomial.C (∏ τ, (atInf (embT D) ((B⁻¹ : GL (Fin (D.R.N 0)) D.host.E) :
          Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^ shiftOf (lamT u 0) τ) *
          subP (fun τ => atInf (embT D) ((B⁻¹ : GL (Fin (D.R.N 0)) D.host.E) :
            Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ) Q) y =
      fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0))
        (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) Q y := by
  have key : ∀ (A z : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ)
      (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ),
      MvPolynomial.eval (fun x => z x.1 x.2.1 x.2.2) (subP A P) =
        MvPolynomial.eval (fun x => (A x.1 * z x.1) x.2.1 x.2.2) P := by
    intro A z P
    induction P using MvPolynomial.induction_on with
    | C a => simp [subP]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [subP, Matrix.mul_apply]
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, map_mul, MvPolynomial.eval_C, Pi.one_apply, Matrix.one_mul]
  rw [key _ (fun τ => y.1 τ)]
  simp only [Matrix.det_mul, mul_zpow, mul_pow, Finset.prod_mul_distrib]
  ring

theorem onto_tL (hRC : RatInC D u) (hRG : RatGL D u) (T : Forms0 D u) (hA : admS D u) (w : D.what₂.places.Pl)
    (hw : OverT D u w) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E)
    (hB : ∀ c, IsLocBasis (D.mem u).A.T (Ld D u 0 (Nat.zero_le _) c : Set _) (B c)) (b : ℤ) :
    (Submodule.pi Set.univ fun _ => (intSubm D w ((D.fm u).lam 0)).map
      (scO (bwA_Ow D w) _ (((D.mem u).A.T : ℂ) ^ b))) ≤ (tL D u w b ((D.fm u).S 0 w)).map (crdL T B w) := by
  intro y hy
  have hy' : ∀ c, ∃ q ∈ intSubm D w ((D.fm u).lam 0), (((D.mem u).A.T : ℂ) ^ b) • q = y c := fun c =>
    hy c (Set.mem_univ c)
  choose Q hQ hQy using hy'
  have hQI : ∀ c, Q c ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0) := fun c => mem_intSubm w _ _ (hQ c)
  obtain ⟨x₀, hx₀⟩ := crd_surj T hA B Q fun c =>
    ⟨_, hRG (fun _ => (B c)⁻¹) _ (intSpan_le_rat w _ (hQI c)), hRC _ (hRG (fun _ => (B c)⁻¹) _ (intSpan_le_rat w _ (hQI c))),
      fun y => fnOf_frame (B c) (Q c) y⟩
  have hx₀S : x₀ ∈ (D.fm u).S 0 w :=
    G0.local_global_lattice_level_zero D u T w hw 0 (Nat.zero_le _) rfl x₀ fun c => ⟨B c, hB c, Q c, hQI c, hx₀ c⟩
  let r : D.what₂.LL := ((D.mem u).A.T : D.what₂.LL) ^ b
  have hr : D.what₂.embLL r = ((D.mem u).A.T : ℂ) ^ b := by
    simp only [r, map_zpow₀, map_natCast]
  refine ⟨r • x₀, ⟨x₀, hx₀S, ?_⟩, ?_⟩
  · rw [LinearMap.map_smulₛₗ, hr]
    rfl
  · funext c
    show crd T B (r • x₀) c = y c
    rw [crd_smul T B r x₀ c, hr, crd_eq T B (hx₀ c), hQy c]

end Formalism.L2.GlobalTheoryTheory.LemB
