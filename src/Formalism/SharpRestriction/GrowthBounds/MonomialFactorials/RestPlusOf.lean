module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusOf
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def phisB (j : Fin G.T.t → ℕ) (jp : ℕ) :
    MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
  (List.finRange G.T.t).foldr (fun i acc =>
    Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
      (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
      ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
      (G.T.z i) ∘ₗ acc) LinearMap.id

def bePhi (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) : ℚ_[p] :=
  Formalism.GM.M.fockK (phisB p (r := r) G j jp u) v / (degFact G j jp : ℚ_[p])

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestPlusA (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
              (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ ≤
      bY C0 CE1 CE2 X aTop x.1 x.2 ⌊D1r C0 CE1 CE2 X CM⌋ * dXi X.r ((X.S C0 CE1 CE2).bPlus - x.2.2)

def RestRankL : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ≤ rL C0 CE1 CE2 X aTop x.1 x.2

def RestPlusB (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    (∑ aPlus ∈ X.winA, (bLvl C0 CE1 CE2 X aTop aPlus x.1 x.2 ⌊X.L.Y * D1r C0 CE1 CE2 X CM⌋ : ℝ)) ≤
      (X.winA.card : ℝ) *
        ((Formalism.GM.M.bad X.p (bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2)
            (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) ⌊D1r C0 CE1 CE2 X CM⌋ : ℝ) +
          5 / X.L.Y * (Module.finrank ℤ_[X.p] (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2) : ℝ))

variable {C0 CE1 CE2 X}

theorem restPlus_of (CM : ℝ) (hY : 0 < X.L.Y) (hA : RestPlusA C0 CE1 CE2 X CM) (hR : RestRankL C0 CE1 CE2 X)
    (hB : RestPlusB C0 CE1 CE2 X CM) : RestPlus C0 CE1 CE2 X CM := by
  intro dl hdl aTop haTop x hx
  have hA' := hA dl hdl aTop haTop x hx
  have hR' := hR dl hdl aTop haTop x hx
  refine (hB dl hdl aTop haTop x hx).trans ?_
  refine mul_le_mul_of_nonneg_left (add_le_add (by exact_mod_cast hA') ?_) (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hR') (div_nonneg (by norm_num) hY.le)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PadicIntegersEmbeddingMapPrime
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Formalism.MainNotions.G

variable (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem castPow_zero (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) :
    ((p ^ n : ℕ) : O ⧸ (IsLocalRing.maximalIdeal O) ^ n) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal O) ^ n)) (p ^ n), Nat.cast_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hpm n

def iotaN (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) :
    ℤ_[p] →+* O ⧸ (IsLocalRing.maximalIdeal O) ^ n :=
  RingHom.comp (ZMod.castHom (ringChar.dvd (castPow_zero p O hpm n)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ n))
    (PadicInt.toZModPow n)

theorem iotaN_compat (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O) hle).comp (iotaN p O hpm n) = iotaN p O hpm m := by
  have hz := PadicInt.zmod_cast_comp_toZModPow (p := p) m n hle
  have key : ∀ (f g : ZMod (p ^ n) →+* O ⧸ (IsLocalRing.maximalIdeal O) ^ m), f = g :=
    fun f g => RingHom.ext_zmod f g
  unfold iotaN
  rw [← hz]
  ext x
  simp only [RingHom.comp_apply]
  exact congrArg (fun f => f (PadicInt.toZModPow n x))
    (key ((Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal O) hle).comp
      (ZMod.castHom (ringChar.dvd (castPow_zero p O hpm n)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ n)))
      ((ZMod.castHom (ringChar.dvd (castPow_zero p O hpm m)) (O ⧸ (IsLocalRing.maximalIdeal O) ^ m)).comp
        (ZMod.castHom (pow_dvd_pow p hle) (ZMod (p ^ m)))))

def iota0 (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : ℤ_[p] →+* O :=
  ((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal O)).symm : AdicCompletion (IsLocalRing.maximalIdeal O) O →+* O).comp
    (AdicCompletion.liftRingHom (IsLocalRing.maximalIdeal O) (iotaN p O hpm) (fun hle => iotaN_compat p O hpm hle))

theorem padic_integers_embedding_map_prime (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) [IsAdicComplete (IsLocalRing.maximalIdeal O) O] :
    iota0 p O hpm (p : ℤ_[p]) = (p : O) :=
  map_natCast (iota0 p O hpm) p

theorem padic_integers_embedding_injective (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : Function.Injective (iota0 p O hpm) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  have hspec := PadicInt.unitCoeff_spec hne
  have h2 := congrArg (iota0 p O hpm) hspec
  rw [hx, map_mul, map_pow, padic_integers_embedding_map_prime] at h2
  have hu : IsUnit (iota0 p O hpm (PadicInt.unitCoeff hne : ℤ_[p])) := (Units.isUnit _).map _
  rcases mul_eq_zero.mp h2.symm with h3 | h3
  · exact hu.ne_zero h3
  · exact hp0 (pow_eq_zero_iff'.mp h3).1

def iotaQ (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] : ℚ_[p] →+* KK O :=
  IsFractionRing.lift (A := ℤ_[p]) (K := ℚ_[p]) (g := (algebraMap O (KK O)).comp (iota0 p O hpm))
    ((IsFractionRing.injective O (KK O)).comp (padic_integers_embedding_injective p O hpm hp0))

theorem iotaQ_int (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hp0 : (p : O) ≠ 0)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : ℤ_[p]) :
    iotaQ p O hpm hp0 (x : ℚ_[p]) = algebraMap O (KK O) (iota0 p O hpm x) := by
  unfold iotaQ
  exact IsFractionRing.lift_algebraMap _ x

def iotaX (X : flipOneThree.Inst) : ℚ_[X.p] →+* KK X.O :=
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal X.O) X.O := X.setting.complete
  iotaQ X.p X.O X.setting.p_mem X.setting.p_ne

theorem iotaX_int (X : flipOneThree.Inst) (x : ℤ_[X.p]) :
    ∃ y : X.O, iotaX X (x : ℚ_[X.p]) = algebraMap X.O (KK X.O) y := by
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal X.O) X.O := X.setting.complete
  exact ⟨_, iotaQ_int X.p X.O X.setting.p_mem X.setting.p_ne x⟩

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.GoodCountMem
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.ProjS

theorem goodCount_mem (p : ℕ) [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℤ_[p] Vs]
    (be : Vs → Vs → ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ) :
    ∃ x y : Fin (goodCount p be L D) → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0 := by
  set S : Set ℕ := {n | ∃ x y : Fin n → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
    ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0} with hS
  have h0 : (0 : ℕ) ∈ S := ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hmem : sSup S ∈ S := by
    by_cases hb : BddAbove S
    · exact Nat.sSup_mem ⟨0, h0⟩ hb
    · rw [Nat.sSup_of_not_bddAbove hb]; exact h0
  exact hmem

section Lin

variable {k σ : Type} [Field k] {r : ℕ}

theorem harmonicProjection_add (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (y y' : MvPolynomial σ k) :
    tieP w e zv sv o n z (y + y') = tieP w e zv sv o n z y + tieP w e zv sv o n z y' := by
  unfold tieP
  simp only [mul_add, map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem harmonicProjection_smul (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (c : k) (y : MvPolynomial σ k) :
    tieP w e zv sv o n z (c • y) = c • tieP w e zv sv o n z y := by
  unfold tieP
  simp only [mul_smul_comm, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _

end Lin

section Block

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem Pall_add (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    G.Pall p (r := r) j jp (u + v) = G.Pall p (r := r) j jp u + G.Pall p (r := r) j jp v := by
  unfold M.BlockData.Pall
  rw [← harmonicProjection_add]
  congr 1
  induction (List.finRange G.T.t) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons]; rw [ih, harmonicProjection_add]

theorem Pall_smul (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    G.Pall p (r := r) j jp (c • u) = c • G.Pall p (r := r) j jp u := by
  unfold M.BlockData.Pall
  rw [← harmonicProjection_smul]
  congr 1
  induction (List.finRange G.T.t) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons]; rw [ih, harmonicProjection_smul]

def Th (j : Fin G.T.t → ℕ) (jp : ℕ) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) : MvPolynomial (M.BVar N r G.T.t) ℚ_[p] :=
  (∏ i, G.Ehat p (r := r) i ^ j i) * G.Eplus p (r := r) ^ jp * G.Pall p (r := r) j jp u

theorem Th_add (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    Th p G j jp (u + v) = Th p G j jp u + Th p G j jp v := by
  unfold Th; rw [Pall_add, mul_add]

theorem Th_smul (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    Th p G j jp (c • u) = c • Th p G j jp u := by
  unfold Th; rw [Pall_smul, mul_smul_comm]

theorem Th_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : Th p (r := r) G j jp (0 : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) = 0 := by
  have := Th_smul p (r := r) G j jp 0 0
  simpa using this

theorem zsmul_eq (c : ℤ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) : c • u = (c : ℚ_[p]) • u :=
  (algebraMap_smul ℚ_[p] c u).symm

theorem Th_mem_PSZ (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hu : u ∈ Ljj p (r := r) G j jp) : Th p G j jp u ∈ G.PSZ p (r := r) := by
  unfold Ljj at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, g, hg, rfl⟩ := hx
    apply Submodule.subset_span
    simp only [Set.mem_iUnion]
    exact ⟨j, jp, hl, y, hy, g, hg, rfl⟩
  | zero => rw [Th_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Th_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [zsmul_eq, Th_smul, ← zsmul_eq]; exact Submodule.smul_mem _ c hx

def lvC (j : Fin G.T.t → ℕ) (jp : ℕ) : ℕ :=
  ((∏ i, (j i).factorial) * jp.factorial) ^ 2 *
    ((∏ i, (((G.lettersAt j jp).deg (G.letterAt (G.T.pos i)) +
        (G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)) + r + G.T.z i + 1 + j i - 1).choose (j i) *
      (G.T.z i).factorial)) *
    (((G.LL.deg G.uPos - jp) + (G.B - jp) + r + G.zPlus + 1 + jp - 1).choose jp * G.zPlus.factorial))

theorem Th_fock (hB : G.BlockOK) (hr : 1 ≤ r) (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp)
    (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : u ∈ Ljj p (r := r) G j jp) (hv : v ∈ Ljj p (r := r) G j jp) :
    fockK (Th p G j jp u) (Th p G j jp v) = (lvC (r := r) G j jp : ℚ_[p]) * fockK u (G.phiAll p (r := r) j jp v) := by
  unfold Ljj at hu hv
  induction hu using Submodule.span_induction with
  | mem x hx =>
    induction hv using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨y, hy, g, hg, rfl⟩ := hx
      obtain ⟨y', hy', g', hg', rfl⟩ := hx'
      have h := (fock_block_decomposition p N r G hB hr).2 j jp hl y hy.1 y' hy'.1 g hg g' hg'
      rw [fockK_smul_left, fockK_smul_right] at h
      have hf : ((∏ i, ((j i).factorial : ℚ_[p])) * (jp.factorial : ℚ_[p])) ≠ 0 :=
        mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      unfold Th lvC
      push_cast
      push_cast at h
      have hf2 : (∏ i, ((j i).factorial : ℚ_[p])) ^ 2 * (jp.factorial : ℚ_[p]) ^ 2 ≠ 0 := by
        rw [← mul_pow]; exact pow_ne_zero 2 hf
      field_simp at h
      rw [div_eq_iff hf2] at h
      rw [h]
      ring
    | zero => rw [Th_zero, fockK_zero_right, map_zero, fockK_zero_right, mul_zero]
    | add a b _ _ ha hb => rw [Th_add, fockK_add_right, ha, hb, map_add (f := _), fockK_add_right, mul_add]
    | smul c a _ ha =>
      rw [zsmul_eq, Th_smul, fockK_smul_right, ha, map_smul, fockK_smul_right]; ring
  | zero => rw [Th_zero, fockK_zero_left, fockK_zero_left, mul_zero]
  | add a b _ _ ha hb => rw [Th_add, fockK_add_left, ha, hb, fockK_add_left, mul_add]
  | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_left, ha, fockK_smul_left]; ring

theorem Th_orth (hB : G.BlockOK) (hr : 1 ≤ r) (j j' : Fin G.T.t → ℕ) (jp jp' : ℕ) (hl : G.LevelOK j jp)
    (hl' : G.LevelOK j' jp') (hne : (j, jp) ≠ (j', jp'))
    (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : u ∈ Ljj p (r := r) G j jp) (hv : v ∈ Ljj p (r := r) G j' jp') :
    fockK (Th p G j jp u) (Th p G j' jp' v) = 0 := by
  unfold Ljj at hu hv
  induction hu using Submodule.span_induction with
  | mem x hx =>
    induction hv using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨y, hy, g, hg, rfl⟩ := hx
      obtain ⟨y', hy', g', hg', rfl⟩ := hx'
      exact (fock_block_decomposition p N r G hB hr).1 j j' jp jp' hl hl' hne y hy.1 y' hy'.1 g hg g' hg'
    | zero => rw [Th_zero, fockK_zero_right]
    | add a b _ _ ha hb => rw [Th_add, fockK_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_right, ha, mul_zero]
  | zero => rw [Th_zero, fockK_zero_left]
  | add a b _ _ ha hb => rw [Th_add, fockK_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_left, ha, mul_zero]

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
