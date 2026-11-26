module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TestSideCounting
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.DgFalseDiag
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OneSidedLemma4
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.SubstSPtrue

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.PrimStep
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TheoremIIClosedOfTestBound
section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ThAllMonomial
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
open Formalism.L2.G.Model (Nv)

abbrev Aset (k d : ℕ) := {α : Fin k →₀ ℕ // ∑ c, α c = d}

instance Aset_finite (k d : ℕ) : Finite (Aset k d) := by
  have : ({α : Fin k →₀ ℕ | ∑ c, α c = d}).Finite := by
    refine (Finset.finite_toSet (Finset.univ.finsuppAntidiag d)).subset ?_
    intro α hα
    simp only [Finset.mem_coe, Finset.mem_finsuppAntidiag]
    exact ⟨hα, Finset.subset_univ _⟩
  exact this.to_subtype

theorem XsFinP (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : (Xs m top vec ν).Finite :=
  (sSIdxFinite (m + 1) (m + 1) ν).subset fun _ he => he.1

instance XsFinP' (m : ℕ) (top vec : Bool) (ν : Fin (m + 1) → ℕ) : Finite (Xs m top vec ν) :=
  (XsFinP m top vec ν).to_subtype

def glue {n' k : ℕ} {d : Fin n' → ℕ} (a : ∀ s, Aset k (d s)) : Fin n' × Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => (a v.1).1 v.2

theorem expand {R : Type} [CommRing R] {n' k : ℕ} {d : Fin n' → ℕ} [Fintype (∀ s, Aset k (d s))]
    (Q : MvPolynomial (Fin n' × Fin k) R) (hQ : IsMultiHom d Q) :
    Q = ∑ a : (∀ s, Aset k (d s)), monomial (glue a) (AddMonoidAlgebra.coeff Q (glue a)) := by
  classical
  ext e
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases he : e ∈ Q.support
  · let a : ∀ s, Aset k (d s) := fun s =>
      ⟨Finsupp.equivFunOnFinite.symm fun c => e (s, c), by simpa using hQ e he s⟩
    have ha : glue a = e := by
      ext v
      rfl
    rw [Finset.sum_eq_single a]
    · rw [if_pos ha, ha]
    · intro a' _ hne
      rw [if_neg]
      intro h
      apply hne
      funext s
      apply Subtype.ext
      ext c
      have := DFunLike.congr_fun (h.trans ha.symm) (s, c)
      exact this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have h0 : AddMonoidAlgebra.coeff Q e = 0 := by simpa using he
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs with h
    · rw [h, h0]
    · rfl

theorem thAll_monomial (F : Type) [CommRing F] (n' m : ℕ) (vec : Fin n' → Bool) (d : Fin n' → ℕ)
    (a : ∀ s, Aset (m + 1) (d s)) (r : F) :
    thAll F n' m vec (monomial (glue a) r) = r • ∏ s, blockEmb F s (∏ c, Nv F m (vec s) c ^ (a s).1 c) := by
  unfold thAll
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Algebra.smul_def]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [map_pow]
  rfl

section Core

variable (F : Type) [Field F] (n' m : ℕ) (vec : Fin n' → Bool) (d : Fin n' → ℕ) {X : Fin n' → Type}
  (b : ∀ s, X s → MvPolynomial (Fin (m + 1) × Fin (m + 1)) F)

def famG (z : (∀ s, Aset (m + 1) (d s)) × (∀ s, X s)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) F :=
  ∏ s, blockEmb F s ((∏ c, Nv F m (vec s) c ^ ((z.1 s).1 c)) * b s (z.2 s))

def fam1 (s : Fin n') (y : Aset (m + 1) (d s) × X s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) F :=
  (∏ c, Nv F m (vec s) c ^ (y.1.1 c)) * b s y.2

def pairUp {n' : ℕ} {A X : Fin n' → Type} (z : (∀ s, A s) × (∀ s, X s)) : ∀ s, A s × X s := fun s => (z.1 s, z.2 s)

theorem pairUp_inj {n' : ℕ} {A X : Fin n' → Type} : Function.Injective (pairUp (A := A) (X := X)) := by
  intro z z' h
  refine Prod.ext ?_ ?_
  · funext s
    exact congrArg Prod.fst (congrFun h s)
  · funext s
    exact congrArg Prod.snd (congrFun h s)

theorem famG_li (hpos : ∀ s, LinearIndependent F (fam1 F n' m vec d b s)) :
    LinearIndependent F (famG F n' m vec d b) := by
  have hli : LinearIndependent F (fun i : (∀ s, Aset (m + 1) (d s) × X s) =>
      ∏ s, blockEmb F s (fam1 F n' m vec d b s (i s))) :=
    ldtensor_prod_linInd_field F (fam1 F n' m vec d b) hpos
  have h2 := hli.comp (pairUp (A := fun s => Aset (m + 1) (d s)) (X := X)) pairUp_inj
  exact h2

theorem famG_sum [Fintype (∀ s, Aset (m + 1) (d s))] (Q : MvPolynomial (Fin n' × Fin (m + 1)) F) (hQ : IsMultiHom d Q)
    (i : ∀ s, X s) :
    (∑ a : (∀ s, Aset (m + 1) (d s)), AddMonoidAlgebra.coeff Q (glue a) • famG F n' m vec d b (a, i)) =
      thAll F n' m vec Q * ∏ s, blockEmb F s (b s (i s)) := by
  have e := expand Q hQ
  have e2 : thAll F n' m vec Q =
      ∑ a : (∀ s, Aset (m + 1) (d s)), AddMonoidAlgebra.coeff Q (glue a) •
        ∏ s, blockEmb F s (∏ c, Nv F m (vec s) c ^ (a s).1 c) := by
    conv_lhs => rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => thAll_monomial F n' m vec d a _
  rw [e2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  unfold famG
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_mul]

theorem big_core [∀ s, Finite (X s)] (hpos : ∀ s, LinearIndependent F (fam1 F n' m vec d b s))
    (J : Finset (∀ s, X s)) (Q : (∀ s, X s) → MvPolynomial (Fin n' × Fin (m + 1)) F) (hQ : ∀ i, IsMultiHom d (Q i))
    (hsum : ∑ i ∈ J, thAll F n' m vec (Q i) * ∏ s, blockEmb F s (b s (i s)) = 0) : ∀ i ∈ J, Q i = 0 := by
  classical
  have : Fintype (∀ s, Aset (m + 1) (d s)) := Fintype.ofFinite _
  have : Fintype (∀ s, X s) := Fintype.ofFinite _
  have hli2 := famG_li F n' m vec d b hpos
  rw [Fintype.linearIndependent_iff] at hli2
  have key := hli2 (fun z => if z.2 ∈ J then AddMonoidAlgebra.coeff (Q z.2) (glue z.1) else 0) ?_
  · intro i hi
    rw [expand (Q i) (hQ i)]
    refine Finset.sum_eq_zero fun a _ => ?_
    have h1 := key (a, i)
    simp only [hi, if_true] at h1
    rw [h1, monomial_zero]
  · rw [Fintype.sum_prod_type_right, ← hsum]
    have h1 : ∀ i : (∀ s, X s),
        (∑ a : (∀ s, Aset (m + 1) (d s)), (if i ∈ J then AddMonoidAlgebra.coeff (Q i) (glue a) else 0) • famG F n' m vec d b (a, i)) =
        if i ∈ J then thAll F n' m vec (Q i) * ∏ s, blockEmb F s (b s (i s)) else 0 := by
      intro i
      by_cases hi : i ∈ J
      · simp only [hi, if_true]
        exact famG_sum F n' m vec d b (Q i) (hQ i) i
      · simp only [hi, if_false, zero_smul, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_ite_mem, Finset.univ_inter]

end Core

theorem bigInd : BigInd := by
  intro F _ n' m hm top vec d ν htop hν b hb J Q hQ hsum
  exact big_core F n' m vec d b
    (fun s => posInd F m hm (top s) (vec s) (d s) (ν s) (htop s) (hν s) (b s) (hb s)) J Q hQ hsum

end Formalism.MainNotions.TestSideCounting
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RestrictedWeightFirstTwoEq
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model (Nv)

theorem map_thAll {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n' m : ℕ) (vec : Fin n' → Bool)
    (P : MvPolynomial (Fin n' × Fin (m + 1)) R) :
    map f (thAll R n' m vec P) = thAll R' n' m vec (map f P) := by
  have hN : ∀ (b : Bool) (c : Fin (m + 1)),
      map f (Formalism.L2.G.Model.Nv R m b c) = Formalism.L2.G.Model.Nv R' m b c := by
    intro b c
    cases b
    · simp only [Formalism.L2.G.Model.Nv, Bool.false_eq_true, if_false]
      have hg : Formalism.L2.G.Model.genM R' m =
          (map f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R →+* _).mapMatrix (Formalism.L2.G.Model.genM R m) := by
        ext a u
        simp [Formalism.L2.G.Model.genM]
      rw [hg, ← RingHom.map_adjugate]
      rfl
    · simp [Formalism.L2.G.Model.Nv]
  have key : (map f).comp (thAll R n' m vec).toRingHom = (thAll R' n' m vec).toRingHom.comp (map f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [thAll]
    · intro v
      simp [thAll, blockEmb, map_rename, hN]
  exact RingHom.congr_fun key P

theorem restricted_weight_first_two_eq {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0)
    (s : Fin n') (hs : s ∈ TT) : restW TT lam0 s 0 = restW TT lam0 s 1 := by
  have hle : lam0 s 1 ≤ lam0 s 0 := hdom s (Fin.zero_le _)
  have h10 : (1 : Fin (m + 1)) ≠ 0 := by
    rw [Ne, Fin.one_eq_zero_iff]
    omega
  have ht := Int.toNat_of_nonneg (sub_nonneg.mpr hle)
  simp only [restW, flW, dT, flatDeg, hs, if_true, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne h10]
  omega

theorem nu_odd {n' m : ℕ} (hm : 1 ≤ m) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0)
    (s : Fin n') (hs : s ∈ TT) (hv : vecE n' s = false) (t : Fin (m + 1)) (ht : m ≤ t.val + 1) :
    nuOf (lamAt (restW TT lam0) s) t = 0 := by
  have hodd : ¬ Even (s : ℕ) := by simpa [vecE] using hv
  have htl := t.isLt
  have hr : restW TT lam0 s t.rev = restW TT lam0 s 0 := by
    have hv' : t.rev.val ≤ 1 := by
      rw [Fin.val_rev]
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv' with h | h
    · have e : t.rev = 0 := Fin.ext (by rw [h, Fin.val_zero])
      rw [e]
    · have e : t.rev = 1 := by
        apply Fin.ext
        rw [h, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
      rw [e, restricted_weight_first_two_eq hm TT lam0 hdom s hs]
  simp only [nuOf, lamAt, hodd, if_false, Fin.rev_last, hr]
  simp

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model (Nv)


set_option maxHeartbeats 1600000 in
theorem primStep_of (hTr : TransStep) (hSub : SubstPol) (C CLa : ℝ) (hSP : SPStep C) : PrimStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  have hm2 : 2 ≤ m := by omega
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  have hwirr : Irreducible w := hSet.2.1
  set ν : Fin n' → Fin (m + 1) → ℕ := fun s => nuOf (lamAt (restW TT lam0) s) with hν
  set top : Fin n' → Bool := fun s => decide (s ∈ TT) with htop
  let I := ∀ s : Fin n', Xs m (top s) (vecE n' s) (ν s)
  have : Finite I := Pi.finite
  let _ : Fintype I := Fintype.ofFinite I
  let eI : I ≃ Fin (Nat.card I) := Finite.equivFin I
  have hbas := fun s => sSBasis O (m + 1) (m + 1) (ν s)
  choose b hb1 hb2 using hbas
  let bX : ∀ s, Xs m (top s) (vecE n' s) (ν s) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) O :=
    fun s y => b s ⟨y.1, y.2.1⟩
  let sO : I → MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) O := fun i => ∏ s, blockEmb O s (bX s (i s))
  have hsO : ∀ i, sO i ∈ tensorLat O O (fun s => dualWeyl O (m + 1) (m + 1) (nuOf (lamAt (restW TT lam0) s))) := by
    intro i
    refine Submodule.subset_span ⟨fun s => bX s (i s), fun s => ?_, rfl⟩
    show bX s (i s) ∈ dualWeyl O (m + 1) (m + 1) (ν s)
    rw [← (hb1 s).2.1]
    exact Submodule.subset_span ⟨_, rfl⟩
  obtain ⟨sh', hsh, hmain⟩ := hTr p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r hm2 (by omega) (by omega) (dT TT lam0)
    (restW TT lam0) lam0 (lambda_zero_eq_product TT lam0) (restW_dom (by omega) TT lam0 hdom) e he hm g hhm hg hbasis Θ hΘ I sO hsO
  refine ⟨Nat.card I, fun i => sh' (eI.symm i), fun i => hsh _, card_all hm2 TT lam0 hdom, ?_⟩
  intro S hS c hcu hmem
  obtain ⟨x0, hx0⟩ := hcu
  obtain ⟨SPO, hSPO1, hSPO2⟩ := hSP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    hrk F hF g hg (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)
  let P : I → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) :=
    fun i => ∑ bb, c (bb, eI i) • FsB bb
  let T0 : I → RRing O n' (r + K) := fun i => ∑ bb, c (bb, eI i) • B bb
  let Q : I → MvPolynomial (Fin n' × Fin (m + 1)) O := fun i => rename (castV hk) (T0 i) * SPO
  have hPQ : ∀ i, subst p n' O w n' r g (P i : MvPolynomial (TV n' (m + 1)) (KK O)) =
      map (algebraMap O (KK O)) (Q i) := by
    intro i
    have e1 : ((P i : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) :
        MvPolynomial (TV n' (m + 1)) (KK O)) =
        ∑ bb, algebraMap O (KK O) (c (bb, eI i)) • (FsB bb : MvPolynomial (TV n' (m + 1)) (KK O)) := by
      simp only [P, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, hFsB, symB, toK, Q, T0, map_mul, map_sum, ← hSPO1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun bb _ => ?_
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_C, mul_assoc]
  have hv : (((∑ y, c y • S y : Vsp Kf lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
      ∑ i, ((Θ (P i) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
        ((sh' i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
    have e2 : ∀ i, ((Θ (P i) : Vsp Kf (flW (m := m) (dT TT lam0))) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ∑ bb, c (bb, eI i) • ((Θ (FsB bb) : Vsp Kf (flW (m := m) (dT TT lam0))) :
          MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [P, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul_of_tower]
    simp only [e2, Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_mul]
    rw [Fintype.sum_prod_type, Finset.sum_comm, ← Equiv.sum_comp eI]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun bb _ => ?_
    rw [hS bb (eI i)]
    simp only [Equiv.symm_apply_apply, smul_mul_assoc]
  obtain ⟨R, hR⟩ := hmain P Q hPQ _ hv hmem

  let Fr := IsLocalRing.ResidueField O
  let res : O →+* Fr := IsLocalRing.residue O
  have hresw : res w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hwirr.not_isUnit
  have h0 : ∑ i ∈ (Finset.univ : Finset I), thAll Fr n' m (vecE n') (map res (Q i)) *
      ∏ s, blockEmb Fr s (map res (bX s (i s))) = 0 := by
    have h1 := congrArg (map res) hR
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_thAll, map_C, hresw, C_0, zero_mul, sO, map_prod, blockEmb, map_rename] at h1
    simpa only [blockEmb] using h1
  have hQhom : ∀ i, IsMultiHom (dT TT lam0) (map res (Q i)) := by
    intro i ee hee s
    have h1 : ee ∈ (Q i).support := support_map_subset res (Q i) hee
    have h2 : ee ∈ (map (algebraMap O (KK O)) (Q i)).support := by
      rw [support_map_of_injective _ (IsFractionRing.injective O (KK O))]
      exact h1
    rw [← hPQ i] at h2
    have h3 := hSub p n' W Qq O Kf ι σ j w hSet.1 φ hφ (m + 1) r (dT TT lam0) g hg _ (P i).2
    exact (Formalism.L2.G.Model.mem_Pol.1 h3) ee h2 s
  have hQ0 := bigInd Fr n' m hm2 top (vecE n') (dT TT lam0) ν
    (fun s hs => by
      have : s ∉ TT := by simpa [htop] using hs
      simp [dT, this])
    (fun s hs hv t ht => nu_odd (by omega) TT lam0 hdom s (by simpa [htop] using hs) hv t ht)
    (fun s y => map res (bX s y))
    (fun s y => by
      obtain ⟨d1, d2, -⟩ := hb2 s ⟨y.1, y.2.1⟩
      have := deg_map (colLex (m + 1) (m + 1)) res (bX s y) d2
      exact ⟨this.1.trans d1, this.2⟩)
    Finset.univ (fun i => map res (Q i)) hQhom h0
  have hq := hQ0 (eI.symm x0.2) (Finset.mem_univ _)
  simp only [Q, map_mul] at hq
  have hT : map res (rename (castV hk) (T0 (eI.symm x0.2))) = 0 := by
    rcases mul_eq_zero.1 hq with h1 | h1
    · exact h1
    · exact absurd h1 hSPO2
  rw [map_rename] at hT
  have hinj : Function.Injective (castV (n' := n') hk) := by
    intro u v huv
    simp only [castV, Prod.mk.injEq] at huv
    exact Prod.ext huv.1 (Fin.cast_injective _ huv.2)
  have hT' : map res (T0 (eI.symm x0.2)) = 0 := by
    apply rename_injective _ hinj
    rw [hT, map_zero]
  have hdvd : MvPolynomial.C w ∣ T0 (eI.symm x0.2) := by
    rw [C_dvd_iff_dvd_coeff]
    intro ee
    have h1 : res (AddMonoidAlgebra.coeff (T0 (eI.symm x0.2)) ee) = 0 := by
      simp only [← coeff_map, hT', AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rw [IsLocalRing.residue_eq_zero_iff, hwirr.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    exact h1
  obtain ⟨y, hy⟩ := hdvd
  obtain ⟨T, hTc⟩ := hc
  have hfin := dvd_of_compl B hli T hTc w (fun bb => c (bb, x0.2)) y (by
    have : T0 (eI.symm x0.2) = ∑ bb, c (bb, x0.2) • B bb := by
      simp only [T0, Equiv.apply_symm_apply]
    rw [← this, hy, MvPolynomial.smul_eq_C_mul]) x0.1
  exact hwirr.not_isUnit (isUnit_of_dvd_unit hfin hx0)

theorem source_integrality_of_substitution (hTr : TransStep) (hSub : SubstPol) (C₀ : ℝ) (hC0 : 0 < C₀) (hSP : ∀ C, C₀ ≤ C → SPStep C)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg :=
  fun _ => ⟨C₀, hC0, fun C hC => primStep_of hTr hSub C CLa (hSP C hC)⟩

end Formalism.MainNotions.TestSideCounting
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.TransStep
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem tr_theta (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m r : ℕ)
    (hm : 1 ≤ m) (d : Fin n' → ℕ) (hmat : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit hmat.det)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (P : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (hP : P ∈ Pol (KK O) (m + 1) d)
    (Q : MvPolynomial (Fin n' × Fin (m + 1)) O) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    subst p n' O w n' r g P = map (algebraMap O (KK O)) Q →
    (algebraMap O Kf w ^ (Avec (vecE n') d)) •
      ((∏ s, (Mx ι σ w φ r (fun x : Fin n' => x) hmat g s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m))) •
        blockAct Kf (Mx ι σ w φ r (fun x : Fin n' => x) hmat g)
          (thF hS m (vecE n') (fun x => la_tw ι σ x.val hmat) P)) =
      map (algebraMap O Kf) (Th0 O m (vecE n') Q) := by
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro hPQ
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hP' := (pol_iff hS _ _ _).1 hP
  have hM := Mx_det (ι := ι) (σ := σ) hw φ r (fun x : Fin n' => x) hmat hh g hg
  unfold thF
  rw [tr_multi_twist Kf m hm (vecE n') d _ hM _ (Lin_Pol _ _ hP'), Lin_comp]
  have h1 := lift_eq hS φ hφ r (LLT n') (fun x : Fin n' => x) (fun _ => rfl) g hg P
  have hB : Bm ι σ w φ r (LLT n').vec (fun x : Fin n' => x) g = fun x => (if (LLT n').vec x then c else 1) •
      (Aa ((LLT n').vec x) (la_tw ι σ x.val hmat)⁻¹ *
        Aa ((LLT n').vec x) (Mx ι σ w φ r (fun x : Fin n' => x) hmat g x)) :=
    funext fun x => Bm_eq hw φ r (LLT n').vec (fun x : Fin n' => x) hmat hh g hg x
  rw [hB, Lin_smul _ _ _ hP'] at h1
  have hprod : ∏ x, (if (LLT n').vec x then c else 1) ^ d x = c ^ Avec (vecE n') d := by
    unfold Avec
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro x _
    show (if vecE n' x then c else 1) ^ d x = _
    split_ifs <;> simp
  rw [hprod] at h1
  have h2 : map (kapR hS) (liftSubst p n' O w r (LLT n') g P) = map (algebraMap O Kf) Q := by
    have : liftSubst p n' O w r (LLT n') g P = map (algebraMap O (KK O)) Q := hPQ
    rw [this, map_map]
    have hk : (kapR hS).comp (algebraMap O (KK O)) = algebraMap O Kf := RingHom.ext fun x => kapR_alg hS x
    rw [hk]
  rw [map_letter_substitution, ← h2, h1, map_smul]
  rfl

end

theorem transStep : TransStep := by
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS φ hφ m r hm hr1 hr2 d rest lam0 hlam hrest e he hmat g hh hg hbasis
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro Θ hΘ I _ sO hsO
  have hfrac := hS.frac_O
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  set M : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf := Mx ι σ w φ r (fun x : Fin n' => x) hmat g with hMdef
  have hM : ∀ s, IsUnit (M s).det := Mx_det hw φ r _ hmat hh g hg
  have hH : ∀ lam : Fin n' → Fin (m + 1) → ℤ, IsDominant lam →
      Hten O lam (fun s => LeAt p ι σ w s.val e) = tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam s) (M s)) := by
    intro lam hl
    unfold Hten
    congr 1
    funext s
    show H0 O m _ (LeAt p ι σ w s.val e) = _
    rw [(edgeLat_of hS m r e _ hbasis).2.1]
    show H0 O m _ (colSpan O (M s)) = _
    rw [H0_eq_twisted_nabla (la_indep hinj) _ _ (lamAt_antitone' lam hl s) _ (hM s)]
  have hV : ∀ lam : Fin n' → Fin (m + 1) → ℤ, IsDominant lam →
      Vsp Kf lam = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam s))) := by
    intro lam hl
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (lamAt_antitone' lam hl s)]
  have hfl : IsDominant (flW (m := m) d) := flW_dom d
  have hl0 : IsDominant lam0 := by rw [hlam]; exact isDominant_add hfl hrest
  let dt : (Fin n' → Fin (m + 1) → ℤ) → Kf := fun lam => ∏ s, (M s).det ^ (lamAt lam s (Fin.last m))
  have hdt : dt lam0 = dt (flW d) * dt rest := by
    show ∏ s, _ = (∏ s, _) * ∏ s, _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [hlam, lamAt_add, Pi.add_apply, zpow_add₀ (hM s).ne_zero]
  have hAr : Ar r lam0 = Ar r (flW (m := m) d) + Ar r rest := by rw [hlam, Ar_add]
  have h1 := fun i => tr_tens_lift O Kf m (fun s => lamAt rest s) M hM (sO i) (hsO i)
  choose y hy1 hy2 using h1
  have hyV : ∀ i, y i ∈ Vsp Kf rest := by
    intro i
    rw [hV rest hrest]
    exact tr_tens_le O Kf m _ M hM _ (hy1 i)
  refine ⟨fun i => c ^ (-Ar r rest) • (⟨y i, hyV i⟩ : Vsp Kf rest), ?_, ?_⟩
  · intro i
    refine ⟨⟨y i, hyV i⟩, ?_, rfl⟩
    show y i ∈ Hten O rest (fun s => LeAt p ι σ w s.val e)
    rw [hH rest hrest]
    exact hy1 i
  · intro P Q hPQ v hv hvmem
    obtain ⟨y0, hy0, hvy⟩ := (mem_scale2 (O := O) (Vsp Kf lam0) (Hten O lam0 fun s => LeAt p ι σ w s.val e)
      (c ^ (1 : ℤ)) (c ^ (-Ar r lam0)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) v).1 hvmem
    rw [hH lam0 hl0] at hy0
    obtain ⟨R0, hR0⟩ := tr_tens_int O Kf m (fun s => lamAt lam0 s) M hM y0 hy0
    refine ⟨R0, ?_⟩
    apply map_injective _ hinj
    have way1 : (c ^ (Ar r lam0) * dt lam0) • blockAct Kf M (v : MvPolynomial _ Kf) =
        map (algebraMap O Kf) (C w * R0) := by
      rw [hvy, map_smul, smul_smul, map_mul, map_C, ← hR0, ← smul_eq_C_mul, smul_smul]
      congr 1
      have hcc : c ^ Ar r lam0 * c ^ (-Ar r lam0) = 1 := by rw [← zpow_add₀ hw, add_neg_cancel, zpow_zero]
      show c ^ Ar r lam0 * dt lam0 * (c ^ (1 : ℤ) * c ^ (-Ar r lam0)) = c * dt lam0
      rw [zpow_one]
      linear_combination (dt lam0 * c) * hcc
    have hA : Ar r (flW (m := m) d) = (Avec (vecE n') d : ℤ) :=
      flat_Ar r hr1 hr2 (vecE n') d (flW d) (isFlat_flW d)
    have hdfl : dt (flW d) = ∏ s, (M s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m)) := by
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [flat_lam (vecE n') d (flW d) (isFlat_flW d) s]
    have way2 : (c ^ (Ar r lam0) * dt lam0) • blockAct Kf M (v : MvPolynomial _ Kf) =
        map (algebraMap O Kf) (∑ i, thAll O n' m (vecE n') (Q i) * sO i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hv, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have t1 := tr_theta hS φ hφ m r (by omega) d hmat hh g hg (P i).1 (P i).2 (Q i) (hPQ i)
      rw [map_mul, map_mul, ← hy2 i]
      have e1 : map (algebraMap O Kf) (thAll O n' m (vecE n') (Q i)) = map (algebraMap O Kf) (Th0 O m (vecE n') (Q i)) :=
        rfl
      rw [e1, ← t1, hΘ (P i), hAr, hdt, hdfl, hA, zpow_add₀ hw, zpow_natCast]
      show _ • (_ * blockAct Kf M (c ^ (-Ar r rest) • y i)) = _
      rw [map_smul]
      simp only [smul_eq_C_mul, map_mul, map_pow]
      have hcc : (C (c ^ Ar r rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * C (c ^ (-Ar r rest)) = 1 := by
        rw [← C_mul, ← zpow_add₀ hw, add_neg_cancel, zpow_zero, C_1]
      linear_combination (C c ^ Avec (vecE n') d * C (∏ s, (M s).det ^ (letterWt m (d s) (vecE n' s) (Fin.last m))) *
        C (dt rest) * blockAct Kf M (thF hS m (vecE n') (fun x => la_tw ι σ x.val hmat) (P i).1) *
        blockAct Kf M (y i)) * hcc
    rw [← way2, way1]

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.Pf14

theorem rest6a (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : SourcePrimitiveIntegrality D CLa Ck Crk Cdeg :=
  source_integrality_of_substitution transStep substPol 1 one_pos (fun C _ => spStep C) D CLa Ck Crk Cdeg

end Formalism.MainNotions.TestSideCounting
end
end

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

def opWord {R : Type} [CommRing R] {n' k : ℕ} (l : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) R) :
    MvPolynomial (Fin n' × Fin k) R :=
  l.foldr (fun y f => X (y.1, y.2.1) * pderiv (y.1, y.2.2) f) f

def OpCl {R : Type} [CommRing R] {n' k : ℕ} (TT : Finset (Fin n')) (c : ℕ)
    (M : Submodule R (MvPolynomial (Fin n' × Fin k) R)) : Submodule R (MvPolynomial (Fin n' × Fin k) R) :=
  Submodule.span R {y | ∃ f ∈ M, ∃ l : List (Fin n' × (Fin k × Fin k)), (∀ z ∈ l, z.1 ∈ TT) ∧
    (∀ s, (l.filter fun z => z.1 = s).length ≤ c) ∧ y = opWord l f}

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n'))
  (lam0 : Fin n' → Fin (m + 1) → ℤ)

def SgOp (c0 : ℕ) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O)) :
    Submodule (KK O) (MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) :=
  OpCl TT c0 (Submodule.span (KK O) (Set.range fun b => (FsB b : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))))

def CloudBAt (c0 loss : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1)) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ κ : ℕ, (κ : ℝ) ≤ bK ∧
    ∀ (n2 : ℕ) (sh : Fin n2 → Vsp Kf (restW TT lam0)), (∀ i, sh i ∈ Re p ι σ w r (restW TT lam0) e) →
      ∀ S : Fin nb × Fin n2 → Vsp Kf lam0,
        (∀ b i, ((S (b, i) : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ((Θ (FsB b) : Vsp Kf (flW (m := m) (dT TT lam0))) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
            ((sh i : Vsp Kf (restW TT lam0)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) →
        ∀ c : Fin nb × Fin n2 → O,
          (∑ x, c x • S x) ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r lam0 e) →
          ∃ F1 : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
            (F1 : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB ∧
            Θ F1 ∈ Re p ι σ w r (flW (dT TT lam0)) e ∧
            Θ F1 ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) ∧
            ∃ (Λ : Module.Dual Kf (Vsp Kf (flW (m := m) (dT TT lam0))) →ₗ[Kf] Module.Dual Kf (Vsp Kf lam0)) (cc : O),
              (∀ T, algebraMap O Kf cc * be p r lam0 (∑ x, c x • S x) (Λ T) =
                (p : Kf) ^ κ * be p r (flW (dT TT lam0)) (Θ F1) T) ∧
              (∀ T ∈ Re' p ι σ w r (flW (dT TT lam0)) e, Λ T ∈ Re' p ι σ w r lam0 e ∧
                be p r lam0 (∑ x, c x • S x) (Λ T) ∈ Set.range (algebraMap O Kf)) ∧
              (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ (i : ℤ),
                ∀ T ∈ scale (algebraMap O Kf w ^ i) (Re' p ι σ w r (flW (dT TT lam0)) e'),
                  Λ T ∈ scale (algebraMap O Kf w ^ (i - loss)) (Re' p ι σ w r lam0 e')) ∧
              (∀ (i : ℤ), ∀ T ∈ scale (algebraMap O Kf w ^ i)
                  (dualLat O Kf (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)),
                Λ T ∈ scale (algebraMap O Kf w ^ (i - loss)) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)))

def FlatAt (c0 cP : ℕ) (bT bD : ℝ) (e : Edge W Qq (m + 1)) {nb : ℕ}
    (FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O))
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0)))) : Prop :=
  ∃ tF DF : ℕ, (tF : ℝ) ≤ bT ∧ (DF : ℝ) ≤ bD ∧
    ∀ F1 : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (F1 : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈ SgOp n' TT lam0 c0 FsB →
      Θ F1 ∈ Re p ι σ w r (flW (dT TT lam0)) e →
      Θ F1 ∉ scale (algebraMap O Kf w ^ (1 : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) →
      ∃ T : Module.Dual Kf (Vsp Kf (flW (m := m) (dT TT lam0))),
        T ∈ scale (algebraMap O Kf w ^ (-(tF : ℤ))) (dualLat O Kf (HL (O := O) ι σ (flW (dT TT lam0)) e.tgt)) ∧
        T ∈ Re' p ι σ w r (flW (dT TT lam0)) e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          T ∈ scale (algebraMap O Kf w ^ (cP : ℤ)) (Re' p ι σ w r (flW (dT TT lam0)) e')) ∧
        ValLe (p : O) DF (be p r (flW (dT TT lam0)) (Θ F1) T)

end At

def CloudBStep (C CK CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        CloudBAt p n' ι σ w r TT lam0 c0 (r * TT.card * c0 + 2 * r * n' * cpp)
          (CK * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e FsB Θ

def FlatStep (C Ct0 CD CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ φ : WF p n' ≃+* W, IsWittIdent σ φ →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')),
      IsUnit hm.det → IsGLW g → IsEdgeBasis p r e (hm * ((matQ φ g)⁻¹).transpose) →
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ FsB : Fin nb → ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O),
      (∀ b, subst p n' O w n' r g (FsB b : MvPolynomial (TV n' (m + 1)) (KK O)) =
        symB p n' O w hk hrk F g (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x) (B b)) →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        FlatAt p n' ι σ w r TT lam0 c0 (cPrime n' r TT.card c0 cpp cStar)
          (t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0)
          (CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) e FsB Θ

def RestCloudB (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ CK C₁ : ℝ, 0 < CK ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → CloudBStep C CK CLa

def RestFlat (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CDf C₁ : ℝ, 0 < Ct0 ∧ 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → FlatStep C Ct0 CDf CLa

theorem test_bound_of_two_halves (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ)
    (hCl : RestCloudB D CLa Ck Crk Cdeg) (hFl : RestFlat D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18) :
    RemainingInputsAfter D CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 := by
  intro hA h14a h14b
  obtain ⟨CK, C₂, hCK, hC2, hC⟩ := hCl hA
  obtain ⟨Ct0, CDf, C₃, h0, h1, hC3, hF⟩ := hFl hA h14a h14b
  refine ⟨Ct0, CK + CDf, max C₂ C₃, h0, by linarith, lt_of_lt_of_le hC2 (le_max_left _ _), ?_⟩
  intro C hCC p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨κ, hκ, hcl⟩ := hC C (le_trans (le_max_left _ _) hCC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y
    cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  obtain ⟨tF, DF, htF, hDF, hfl⟩ := hF C (le_trans (le_max_right _ _) hCC) p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0
    aT bT a Y cpp c0 Dp cStar hSet H φ hφ K hk hrk F hFr E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis FsB hFsB Θ hΘ
  refine ⟨tF + (r * TT.card * c0 + 2 * r * n' * cpp), κ + DF, ?_, ?_, ?_⟩
  · unfold om
    push_cast
    linarith
  · push_cast
    have e1 : (CK + CDf) * (TT.card : ℝ) * ((m : ℝ) + 1) ^ 2 * Real.logb p a =
        CK * (TT.card : ℝ) * ((m : ℝ) + 1) ^ 2 * Real.logb p a + CDf * (TT.card : ℝ) * ((m : ℝ) + 1) ^ 2 * Real.logb p a := by
      ring
    push_cast at hκ hDF
    rw [e1]
    linarith
  intro n2 sh hsh S hS c hv
  obtain ⟨F1, f1, f2, f3, Λ, cc, l1, l2, l3, l4⟩ := hcl n2 sh hsh S hS c hv
  obtain ⟨T, t1, t2, t3, t4⟩ := hfl F1 f1 f2 f3
  refine ⟨Λ T, ?_, (l2 T t2).1, ?_, ?_⟩
  · have := l4 _ T t1
    convert this using 3
    push_cast
    ring
  · intro e' he' htg hne
    have := l3 e' he' htg _ T (t3 e' he' htg hne)
    convert this using 3
    unfold cPrime
    push_cast
    ring
  · obtain ⟨aa, haa⟩ := (l2 T t2).2
    obtain ⟨y, b', hy, hyb⟩ := t4
    refine ⟨aa, cc * b', haa.symm, ?_⟩
    have hinj : Function.Injective (algebraMap O Kf) := by
      have := hSet.1.frac_O
      exact IsFractionRing.injective O Kf
    apply hinj
    have h5 := l1 T
    rw [← haa, hy] at h5
    have : algebraMap O Kf (aa * (cc * b')) = (algebraMap O Kf cc * algebraMap O Kf aa) * algebraMap O Kf b' := by
      simp only [map_mul]; ring
    rw [this, h5, mul_assoc, ← map_mul, hyb]
    simp [pow_add]

end Formalism.MainNotions.TestSideCounting
