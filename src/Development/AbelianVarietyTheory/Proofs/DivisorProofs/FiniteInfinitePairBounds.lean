module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightsTopGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingIntegralUpToExponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCut
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingArchimedeanBoundFockNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanBranchingConstantBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVertexLatticeOrthonormalCoordsTopNodeIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLatSplit

open _root_.Formalism.L2.Col.Br

private theorem forall_idx {N n : ℕ} (hN : N = n + 1) (p : Fin N → Prop) :
    (∀ i, p i) ↔ (∀ k, p (iC hN k)) ∧ p (iL hN) := by
  subst hN
  exact Fin.forall_fin_succ'

private theorem frame_mulVec {R : Type} [CommRing R] {N n : ℕ} (hN : N = n + 1) (Fr : Matrix (Fin N) (Fin N) R)
    (Q : Matrix (Fin N) (Fin n) R) (a : Fin N → R) (hC : ∀ i k, Fr i (iC hN k) = Q i k) (hL : ∀ i, Fr i (iL hN) = a i)
    (t : Fin N → R) : Fr *ᵥ t = Q *ᵥ (fun k => t (iC hN k)) + t (iL hN) • a := by
  subst hN
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hC, ← hL]
  rw [Fin.sum_univ_castSucc, mul_comm (t _)]
  rfl

private theorem block {R : Type} [CommRing R] {N n : ℕ} (hN : N = n + 1) (A Fr : GL (Fin N) R) (B fr : GL (Fin n) R)
    (P : Matrix (Fin N) (Fin n) R) (a : Fin N → R) (hP : A.val * P = P * B.val) (ha : A.val *ᵥ a = a)
    (hC : ∀ i k, Fr.val i (iC hN k) = (P * fr.val) i k) (hL : ∀ i, Fr.val i (iL hN) = a i) (v : Fin N → R) :
    (∀ k, (((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v) (iC hN k) = (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC hN k)) k) ∧
      (((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v) (iL hN) = v (iL hN) := by
  obtain ⟨z, hzC, hzL⟩ : ∃ z : Fin N → R, (∀ k, z (iC hN k) = (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC hN k)) k) ∧
      z (iL hN) = v (iL hN) := by
    subst hN
    refine ⟨Fin.snoc (α := fun _ => R) (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC rfl k)) (v (iL rfl)), fun k => ?_, ?_⟩
    · exact Fin.snoc_castSucc (α := fun _ => R) _ _ k
    · exact Fin.snoc_last (α := fun _ => R) _ _
  have e1 : B.val * fr.val * ((fr⁻¹ * B * fr)⁻¹).val = fr.val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e2 : A.val *ᵥ (Fr.val *ᵥ z) = Fr.val *ᵥ v := by
    rw [frame_mulVec hN Fr.val _ a hC hL z, frame_mulVec hN Fr.val _ a hC hL v, funext hzC, hzL, Matrix.mulVec_add,
      Matrix.mulVec_smul, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hP, Matrix.mul_assoc P,
      Matrix.mul_assoc P, e1]
  have e3 : ((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v = z := by
    have e4 : (Fr⁻¹ * A * Fr).val *ᵥ z = v := by
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_mulVec,
        Units.inv_mul, Matrix.one_mulVec]
    rw [← e4, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [e3]
  exact ⟨hzC, hzL⟩

private theorem mem_latAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X)
    (v : Fin (G.V X).rank → D.host.E) :
    v ∈ GlobalTheory.SumSize.latAt S X x ↔ ∀ i, ((((Formalism.UG.bc (eToEAf D) (S.N.fr X))⁻¹ *
      (Lev.finE (G.V X) x.1 * Lev.finE (G.V X) (S.N.u X).1) * Formalism.UG.bc (eToEAf D) (S.N.fr X))⁻¹).val *ᵥ
        fun i => eToEAf D (v i)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [← map_inv]
  exact (GlobalTheory.MovedSD.mem_globLat_move D (G.Λ X) (S.N.fr X) _ _ (S.N.u_lat X hX) v).trans (Formalism.L2.Col.mem_latS_std _)

private theorem finE_val {D : D7} (V : HSp D) (g : Formalism.L2.Theta.GA D V) : (Lev.finE V g).val = (mt V g).map (toEAf D) := by
  ext i j
  rfl

private theorem emb_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N n : ℕ} (x u : Matrix (Fin N) (Fin N) R)
    (y u' : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin N) (Fin n) R) (hx : x * P = P * y) (hu : u * P = P * u') :
    x.map f * u.map f * P.map f = P.map f * (y.map f * u'.map f) := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc, hu, ← Matrix.mul_assoc, hx,
    Matrix.mul_assoc]

private theorem vec_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N : ℕ} (x u : Matrix (Fin N) (Fin N) R)
    (a : Fin N → R) (hx : x *ᵥ a = a) (hu : u *ᵥ a = a) :
    (x.map f * u.map f) *ᵥ (fun i => f (a i)) = fun i => f (a i) := by
  funext i
  rw [← Matrix.map_mul]
  refine (RingHom.map_mulVec f (x * u) a i).symm.trans ?_
  rw [← Matrix.mulVec_mulVec, hu, hx]

end GlobalTheory.TopLatSplit

open GlobalTheory.TopLatSplit in
set_option maxHeartbeats 800000 in
theorem _root_.GlobalTheory.T.mem_vertexLatticeOrthonormalCoords_topNode_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)) (v : Fin (G.V (.top D.R.m)).rank → D.host.E),
    v ∈ GlobalTheory.SumSize.latAt S (.top D.R.m) (finEmb G.sp.topDec y) ↔
      (fun k => v (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k)) ∈ GlobalTheory.SumSize.latAt S (.grid D.R.m D.R.m) y ∧
        ∃ c : 𝓞 D.host.E, (c : D.host.E) = v (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) := by
  intro D T L sc G W S y v
  have hrel := finEmb_rel G.sp.topDec y
  have hx1 : mt (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 * topEmb G = topEmb G * mt (G.V (.grid D.R.m D.R.m)) y.1 := hrel.1
  have hx2 : mt (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 *ᵥ topVec G = topVec G :=
    hrel.2 (fun i => G.sp.topDec.a i 0) (funext fun k => congr_fun (congr_fun G.sp.topDec.perp k) 0)
  have hb := block (R := Lev.EAf D) (N := (G.V (.top D.R.m)).rank) (n := (G.V (.grid D.R.m D.R.m)).rank) G.sp.topDec.rank.symm
    (Lev.finE (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 * Lev.finE (G.V (.top D.R.m)) (S.N.u (.top D.R.m)).1)
    (Formalism.UG.bc (eToEAf D) (S.N.fr (.top D.R.m)))
    (Lev.finE (G.V (.grid D.R.m D.R.m)) y.1 * Lev.finE (G.V (.grid D.R.m D.R.m)) (S.N.u (.grid D.R.m D.R.m)).1)
    (Formalism.UG.bc (eToEAf D) (S.N.fr (.grid D.R.m D.R.m)))
    ((topEmb G).map (toEAf D)) (fun i => toEAf D (topVec G i))
    (by
      rw [Units.val_mul, Units.val_mul, finE_val, finE_val, finE_val, finE_val]
      exact emb_map (toEAf D) _ _ _ _ _ hx1 S.N.u_top)
    (by
      rw [Units.val_mul, finE_val, finE_val]
      exact vec_map (toEAf D) _ _ _ hx2 S.N.u_last)
    (fun i k => by
      have e := congrArg (eToEAf D) (S.N.fr_top i k)
      exact e.trans (congr_fun (congr_fun (Matrix.map_mul (f := eToEAf D)) i) k))
    (fun i => congrArg (eToEAf D) (S.N.fr_last i))
    (fun i => eToEAf D (v i))
  refine (mem_latAt S (.top D.R.m) (le_refl D.R.m) (finEmb G.sp.topDec y) v).trans ?_
  refine (forall_idx (N := (G.V (.top D.R.m)).rank) (n := (G.V (.grid D.R.m D.R.m)).rank) G.sp.topDec.rank.symm _).trans ?_
  refine and_congr ?_ ?_
  · refine Iff.trans ?_ (mem_latAt S (.grid D.R.m D.R.m) ⟨le_refl _, rfl⟩ y _).symm
    exact forall_congr' fun k => Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hb.1 k))
  · refine (Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) hb.2)).trans ?_
    exact GlobalTheory.NormSum.AdLattice.incl_mem_iff _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceValuationLocalDegreeArithmetic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceValuationLocalDegreeArithmetic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem vw_lw_arith : ∀ {K : Type} [Field K] [NumberField K] [StarRing K],
    (∀ (w : HeightOneSpectrum (𝓞 K)) (a b : K), a ≠ 0 → b ≠ 0 → Formalism.DivisionValues.vw w (a * b) = Formalism.DivisionValues.vw w a + Formalism.DivisionValues.vw w b) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (m d : ℕ), 0 < d → m ∣ d →
      0 ≤ Formalism.DivisionValues.vw w (m : K) ∧ Formalism.DivisionValues.vw w (m : K) ≤ Formalism.DivisionValues.vw w (d : K)) ∧
    (∀ d : ℕ, 0 < d → {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.vw w (d : K) ≠ 0}.Finite) ∧
    (∀ d : ℕ, 0 < d → ∀ s : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ w ∈ s, Formalism.DivisionValues.lw w * (Formalism.DivisionValues.vw w (d : K) : ℝ) ≤ Real.log d) := by
  intro K _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w a b ha hb
    exact Formalism.DivisionValues.ValuationRepresentative.vw_mul w a b ha hb
  · intro w m d hd hmd
    obtain ⟨k, rfl⟩ := hmd
    have hm0 : m ≠ 0 := by rintro rfl; simp at hd
    have hk0 : k ≠ 0 := by rintro rfl; simp at hd
    have hnn : ∀ n : ℕ, 0 ≤ Formalism.DivisionValues.vw w (n : K) := by
      intro n
      have h := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w ((n : ℕ) : 𝓞 K)
      simpa using h
    refine ⟨hnn m, ?_⟩
    rw [Nat.cast_mul, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (by exact_mod_cast hm0) (by exact_mod_cast hk0)]
    linarith [hnn k]
  · intro d hd
    have hf := FractionalIdeal.finite_factors (K := K)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (d : K))
    rw [Filter.eventually_cofinite] at hf
    refine hf.subset ?_
    intro w hw
    exact hw
  · intro d hd s
    exact Formalism.EigenvalueLevelCeiling.sum_lw_vw_natCast_le s d hd.ne'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceValuationLocalDegreeArithmeticStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeValuation_localDegree_arithmetic : ∀ {K : Type} [Field K] [NumberField K] [StarRing K],
    (∀ (w : HeightOneSpectrum (𝓞 K)) (a b : K), a ≠ 0 → b ≠ 0 → Formalism.DivisionValues.vw w (a * b) = Formalism.DivisionValues.vw w a + Formalism.DivisionValues.vw w b) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (m d : ℕ), 0 < d → m ∣ d →
      0 ≤ Formalism.DivisionValues.vw w (m : K) ∧ Formalism.DivisionValues.vw w (m : K) ≤ Formalism.DivisionValues.vw w (d : K)) ∧
    (∀ d : ℕ, 0 < d → {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.vw w (d : K) ≠ 0}.Finite) ∧
    (∀ d : ℕ, 0 < d → ∀ s : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ w ∈ s, Formalism.DivisionValues.lw w * (Formalism.DivisionValues.vw w (d : K) : ℝ) ≤ Real.log d) := by
  first | exact @GlobalTheory.vw_lw_arith | exact GlobalTheory.vw_lw_arith | (intros; apply GlobalTheory.vw_lw_arith <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotalExponentTopWeightBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinSize

open Finset

private def extN {n : ℕ} (ν : Fin n → ℕ) : ℕ → ℕ := fun i => if h : i < n then ν ⟨i, h⟩ else 0

private theorem res_extN {n : ℕ} (ν : Fin n → ℕ) : Formalism.CohomologicalDescent.LD.res n (extN ν) = ν := by
  funext i
  simp [Formalism.CohomologicalDescent.LD.res, extN, i.2]

private theorem exZ_le_of_width {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (w : ℕ)
    (hw : ∀ a : Fin n, ν a + (n - 1 - a) ≤ w) (l : ℕ) (hl : l.Prime) :
    Formalism.CohomologicalDescent.LA.exZ n n le_rfl ν l ≤ n.choose 2 * Nat.log l w ∧
      (w < l → Formalism.CohomologicalDescent.LA.exZ n n le_rfl ν l = 0) := by
  have hanti : Antitone (Formalism.CohomologicalDescent.LD.res n (extN ν)) := by rw [res_extN]; exact hν
  have hI : ∀ a < n, (0 : ℤ) ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN n (extN ν) a ∧
      Formalism.CohomologicalDescent.UnitNormBounds.UN n (extN ν) a ≤ 0 + (w : ℤ) := by
    intro a ha
    have h := hw ⟨a, ha⟩
    simp only [Formalism.CohomologicalDescent.UnitNormBounds.UN, extN, ha, dif_pos]
    simp only at h
    constructor <;> omega
  have h := Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut GlobalTheory.LeviCut.exCut n (extN ν) hanti l hl 0 w hI
  rwa [res_extN] at h

private theorem natW_wtOf_add_le (n : ℕ) (E : Finset ℚ) (lo hi : ℝ) (hE : ∀ x ∈ E, lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi) (w : ℕ)
    (hw : hi - lo ≤ w) (hn : n - 1 ≤ w) (a : Fin n) :
    (GlobalTheory.FunObj.wtOf n E).natW a + (n - 1 - a) ≤ w := by
  have hpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) a.2
  have ha := a.2
  unfold GlobalTheory.FunObj.wtOf
  split_ifs with h
  · obtain ⟨z, hz⟩ := GlobalTheory.SignedHC.highestWeight_int h.1 h.2 a
    obtain ⟨z', hz'⟩ := GlobalTheory.SignedHC.highestWeight_int h.1 h.2 ⟨n - 1, by omega⟩
    simp only [Formalism.BasicNotions.DomWeight.natW, Formalism.BasicNotions.DomWeight.detShift, dif_pos hpos, hz, hz', Int.floor_intCast]
    have e1 : (z : ℚ) = GlobalTheory.SignedHC.descEnum E h.1 a - (((n : ℚ) - 1) / 2 - ((a : ℕ) : ℚ)) := hz.symm
    have e2 : (z' : ℚ) = GlobalTheory.SignedHC.descEnum E h.1 ⟨n - 1, by omega⟩ -
        (((n : ℚ) - 1) / 2 - ((n - 1 : ℕ) : ℚ)) := hz'.symm
    have e1R : (z : ℝ) = (GlobalTheory.SignedHC.descEnum E h.1 a : ℝ) - (((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) e1
      push_cast at this
      exact this
    have e2R : (z' : ℝ) = (GlobalTheory.SignedHC.descEnum E h.1 ⟨n - 1, by omega⟩ : ℝ) -
        (((n : ℝ) - 1) / 2 - ((n - 1 : ℕ) : ℝ)) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) e2
      push_cast at this
      exact this
    have m1 := hE _ (GlobalTheory.SignedHC.descEnum_mem E h.1 a)
    have m2 := hE _ (GlobalTheory.SignedHC.descEnum_mem E h.1 ⟨n - 1, by omega⟩)
    have c1 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) + 1 + ((a : ℕ) : ℝ) = n := by
      have : n - 1 - (a : ℕ) + 1 + (a : ℕ) = n := by omega
      exact_mod_cast this
    have c2 : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      have : n - 1 + 1 = n := by omega
      exact_mod_cast this
    have key : (((z - z' : ℤ) : ℝ)) + ((n - 1 - (a : ℕ) : ℕ) : ℝ) ≤ w := by
      push_cast
      linarith [m1.1, m1.2, m2.1, m2.2]
    have key' : (z - z') + ((n - 1 - (a : ℕ) : ℕ) : ℤ) ≤ w := by exact_mod_cast key
    omega
  · simp only [Formalism.BasicNotions.DomWeight.natW, Formalism.BasicNotions.DomWeight.detShift, Pi.zero_apply, dite_eq_ite, ite_self,
      sub_zero, Int.toNat_zero, zero_add]
    omega

private theorem exists_prod_bound (w A : ℕ) (e : ℕ → ℕ)
    (he : ∀ p : ℕ, p.Prime → e p ≤ A * Nat.log p w ∧ (w < p → e p = 0)) :
    ∃ Dn : ℕ, 0 < Dn ∧ (∀ p : ℕ, p.Prime → p ^ e p ∣ Dn) ∧
      Real.log Dn ≤ (A : ℝ) * w * Real.log w := by
  classical
  set S := (Finset.range (w + 1)).filter Nat.Prime with hS
  refine ⟨∏ p ∈ S, p ^ e p, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.1 hp).2.pos _
  · intro p hp
    by_cases hpw : p ≤ w
    · exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)
    · rw [(he p hp).2 (by omega), pow_zero]
      exact one_dvd _
  · rw [Nat.cast_prod, Real.log_prod (fun p hp => by
        have := (Finset.mem_filter.1 hp).2.pos
        exact_mod_cast (pow_pos this (e p)).ne')]
    have hterm : ∀ p ∈ S, Real.log ((p ^ e p : ℕ) : ℝ) ≤ A * Real.log w := by
      intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      have hpw : p ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_filter.1 hp).1)
      have hw0 : w ≠ 0 := by have := hp'.two_le; omega
      rw [Nat.cast_pow, Real.log_pow]
      have h1 : (e p : ℝ) ≤ A * Nat.log p w := by exact_mod_cast (he p hp').1
      have h2 : (Nat.log p w : ℝ) * Real.log p ≤ Real.log w := by
        have h3 := Nat.pow_log_le_self p hw0
        rw [← Real.log_pow]
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp'.pos
        apply Real.log_le_log (by positivity)
        exact_mod_cast h3
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)
      calc (e p : ℝ) * Real.log p ≤ (A * Nat.log p w) * Real.log p := mul_le_mul_of_nonneg_right h1 hlogp
        _ = A * ((Nat.log p w : ℝ) * Real.log p) := by ring
        _ ≤ A * Real.log w := mul_le_mul_of_nonneg_left h2 (by positivity)
    have hcard : S.card ≤ w := by
      calc S.card ≤ (Finset.Icc 1 w).card := Finset.card_le_card (fun p hp => by
              have h1 := Finset.mem_filter.1 hp
              have h2 := h1.2.one_lt
              have h3 := Finset.mem_range.1 h1.1
              rw [Finset.mem_Icc]
              omega)
        _ = w := by simp
    have hlw : 0 ≤ Real.log w := Real.log_natCast_nonneg w
    calc ∑ p ∈ S, Real.log ((p ^ e p : ℕ) : ℝ) ≤ ∑ p ∈ S, (A : ℝ) * Real.log w := Finset.sum_le_sum hterm
      _ = S.card * (A * Real.log w) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ w * (A * Real.log w) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) hlw)
          exact_mod_cast hcard
      _ = A * w * Real.log w := by ring

end GlobalTheory.FinSize

namespace GlobalTheory.FinSize

open Finset GlobalTheory.SignedHC

private theorem entries_top_bound (D : D7) (large₂ : SizeData₂ D) (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (τ : D.what₂.Tau)
    (C : ℝ) (hC : C = 1) :
    ∀ x ∈ GlobalTheory.SignedHC.entries (Node.par D C (.top D.R.m) τ),
      -(6 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
  subst hC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSc, hbe, -⟩ := hS
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hga : 2 * bigN D ^ 3 + 2 * sLen D + 3 ≤ gap D 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN3 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have htN : D.R.t ≤ bigN D := by
    unfold bigN
    have h1 : D.R.t ≤ D.R.m * (D.R.t + sLen D + 1) :=
      le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) (Nat.le_mul_of_pos_left _ (by omega))
    exact le_trans h1 (Nat.le_add_left _ _)
  have hScpos := large₂.Sc_pos
  have htga : (D.R.t : ℝ) + 3 ≤ (gap D 1 : ℝ) := by exact_mod_cast (by omega : D.R.t + 3 ≤ gap D 1)
  have hm1 : (3 : ℝ) ≤ (D.R.m : ℝ) + 1 := by
    have : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
    linarith
  have hga0 : (0 : ℝ) ≤ (gap D 1 : ℝ) := Nat.cast_nonneg _
  have hmγ : (gap D 1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by nlinarith
  have htb : (D.R.t : ℝ) ≤ large₂.sc.b := by linarith
  have hb1 : 3 ≤ large₂.sc.b := by linarith
  set G := num D 1 τ with hG
  have hGm : G.m = D.R.m := rfl
  have hGga : G.ga = gap D 1 := rfl
  have hGt : G.t = D.R.t := rfl
  have hSc' : large₂.Sc + ((G.m : ℝ) + 1) * (G.ga : ℝ) + 1 / 2 ≤ large₂.sc.b := hSc
  have hmγ' : (0 : ℝ) ≤ ((G.m : ℝ) + 1) * (G.ga : ℝ) := by positivity
  have hv : ∀ i, 2 ≤ i → i ≤ D.R.k → (-1 : ℝ) ≤ ((G.v i : ℤ) : ℝ) ∧ ((G.v i : ℤ) : ℝ) ≤ large₂.Sc := by
    intro i h1 h2
    have hi : i - 2 < D.R.k - 1 := by omega
    have hc := large₂.cloud_v τ ⟨i - 2, hi⟩
    have e : G.v i = ⌊(D.hc τ).v ⟨i - 2, hi⟩⌋ := by
      show GlobalTheory.SignedHC.GridData.extend 2 (D.hc τ).v i = _
      unfold GlobalTheory.SignedHC.GridData.extend
      rw [dif_pos hi]
    rw [e]
    have f1 : ((⌊(D.hc τ).v ⟨i - 2, hi⟩⌋ : ℤ) : ℚ) ≤ (D.hc τ).v ⟨i - 2, hi⟩ := Int.floor_le _
    have f2 : (D.hc τ).v ⟨i - 2, hi⟩ < ((⌊(D.hc τ).v ⟨i - 2, hi⟩⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
    have g1 : ((⌊(D.hc τ).v ⟨i - 2, hi⟩⌋ : ℤ) : ℝ) ≤ (((D.hc τ).v ⟨i - 2, hi⟩ : ℚ) : ℝ) := by exact_mod_cast f1
    have g2 : (((D.hc τ).v ⟨i - 2, hi⟩ : ℚ) : ℝ) < ((⌊(D.hc τ).v ⟨i - 2, hi⟩⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast f2
    constructor <;> linarith [hc.1, hc.2]
  have he : ∀ l, 1 ≤ l → l ≤ D.R.m → (-1 : ℝ) ≤ ((G.e l : ℤ) : ℝ) ∧ ((G.e l : ℤ) : ℝ) ≤ 4 * large₂.sc.b := by
    intro l h1 h2
    have hl : l - 1 < D.R.m := by omega
    have hc := hbe τ ⟨l - 1, hl⟩
    have hgap := (D.hc τ).gap_be ⟨l - 1, hl⟩
    have e : G.e l = ⌊(D.hc τ).e ⟨l - 1, hl⟩⌋ := by
      show GlobalTheory.SignedHC.GridData.extend 1 (D.hc τ).e l = _
      unfold GlobalTheory.SignedHC.GridData.extend
      rw [dif_pos hl]
    rw [e]
    have hpos : (0 : ℚ) < (D.hc τ).e ⟨l - 1, hl⟩ := by
      have h0 : (0 : ℚ) < (D.hc τ).b ⟨l - 1, hl⟩ := by exact_mod_cast hc.1
      have h3 : (0 : ℚ) ≤ (D.R.t : ℚ) := Nat.cast_nonneg _
      linarith
    have f1 : ((⌊(D.hc τ).e ⟨l - 1, hl⟩⌋ : ℤ) : ℚ) ≤ (D.hc τ).e ⟨l - 1, hl⟩ := Int.floor_le _
    have f2 : (D.hc τ).e ⟨l - 1, hl⟩ < ((⌊(D.hc τ).e ⟨l - 1, hl⟩⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
    have g1 : ((⌊(D.hc τ).e ⟨l - 1, hl⟩⌋ : ℤ) : ℝ) ≤ (((D.hc τ).e ⟨l - 1, hl⟩ : ℚ) : ℝ) := by exact_mod_cast f1
    have g2 : (((D.hc τ).e ⟨l - 1, hl⟩ : ℚ) : ℝ) < ((⌊(D.hc τ).e ⟨l - 1, hl⟩⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast f2
    have g3 : (0 : ℝ) < (((D.hc τ).e ⟨l - 1, hl⟩ : ℚ) : ℝ) := by exact_mod_cast hpos
    have g4 : (((D.hc τ).e ⟨l - 1, hl⟩ : ℚ) : ℝ) ≤ 4 * large₂.sc.b := hc.2
    constructor <;> linarith
  have hv2 := hv 2 le_rfl (by omega)
  intro x hx
  have hx' : x ∈ G.weightX D.R.m := by
    rw [show Node.par D 1 (.top D.R.m) τ = GlobalTheory.SignedHC.plus (G.weightX D.R.m) from rfl,
      GlobalTheory.SignedHC.entries_plus] at hx
    exact hx
  rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx' with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
    have hiR : (i : ℝ) ≤ (G.m : ℝ) := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    have p1 : 0 ≤ ((G.m : ℝ) + 1 - i) * (G.ga : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have p2 : ((G.m : ℝ) + 1 - i) * (G.ga : ℝ) ≤ ((G.m : ℝ) + 1) * (G.ga : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    simp only [GlobalTheory.SignedHC.GridData.a]
    push_cast
    constructor <;> linarith
  · obtain ⟨i, h1, h2, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
    have hvi := hv i h1 h2
    simp only [GlobalTheory.SignedHC.GridData.vHalf]
    push_cast
    constructor <;> linarith
  · have hb := GlobalTheory.ChiGrid.blockC'_between (num_nearMid D 1 τ) (odd_sLen D).pos (sLen_lt_gap D 1) h1 h2 h
    have c1 : ((G.a i : ℚ) : ℝ) < (x : ℝ) := by exact_mod_cast hb.1
    have c2 : (x : ℝ) < ((G.a i + G.ga : ℚ) : ℝ) := by exact_mod_cast hb.2
    simp only [GlobalTheory.SignedHC.GridData.a] at c1 c2
    push_cast at c1 c2
    have hiR : (i : ℝ) ≤ (G.m : ℝ) := by exact_mod_cast h2
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h1
    have p1 : 0 ≤ ((G.m : ℝ) + 1 - i) * (G.ga : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have p2 : ((G.m : ℝ) + 1 - i) * (G.ga : ℝ) + (G.ga : ℝ) ≤ ((G.m : ℝ) + 1) * (G.ga : ℝ) := by
      have : ((G.m : ℝ) + 1 - i) * (G.ga : ℝ) + (G.ga : ℝ) = ((G.m : ℝ) + 1) * (G.ga : ℝ) - (i - 1) * (G.ga : ℝ) := by
        ring
      rw [this]
      have : 0 ≤ ((i : ℝ) - 1) * (G.ga : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
      linarith
    constructor <;> linarith
  · have hab := abs_le.1 (GlobalTheory.SignedHC.abs_sub_le_of_mem_block h)
    have hel := he l h1 h2
    have c1 : (x : ℝ) ≤ -((G.e l : ℤ) : ℝ) + (G.t : ℝ) / 2 := by
      have h' : x ≤ -((G.e l : ℤ) : ℚ) + (G.t : ℚ) / 2 := by push_cast at hab; linarith [hab.2]
      have h'' : (x : ℝ) ≤ ((-((G.e l : ℤ) : ℚ) + (G.t : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.2 h'
      push_cast at h''
      linarith
    have c2 : -((G.e l : ℤ) : ℝ) - (G.t : ℝ) / 2 ≤ (x : ℝ) := by
      have h' : -((G.e l : ℤ) : ℚ) - (G.t : ℚ) / 2 ≤ x := by push_cast at hab; linarith [hab.1]
      have h'' : ((-((G.e l : ℤ) : ℚ) - (G.t : ℚ) / 2 : ℚ) : ℝ) ≤ (x : ℝ) := Rat.cast_le.2 h'
      push_cast at h''
      linarith
    have htb' : (G.t : ℝ) ≤ large₂.sc.b := htb
    have ht0 : (0 : ℝ) ≤ (G.t : ℝ) := Nat.cast_nonneg _
    constructor <;> linarith

private theorem rank_top {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    (G.V (.top D.R.m)).rank = bigN D := by
  have hm := D.R.two_le_m
  have key : ∀ j, 1 ≤ j → j ≤ D.R.m → (G.V (.top j)).rank = rankX D j := by
    intro j h1 h2
    cases j with
    | zero => omega
    | succ j => exact (G.sp.X_is (j + 1) h1 h2).rank
  rw [key D.R.m (by omega) le_rfl]
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Ranks.r; omega
  simp only [rankX, rankP, nRk, bigN, sLen]
  rw [show D.R.r + 6 - 1 = D.R.r + 5 by omega, hr]
  ring

end GlobalTheory.FinSize

namespace GlobalTheory.FinSize

private theorem natW_anti' {n : ℕ} (l : Formalism.BasicNotions.DomWeight n) : Antitone l.natW := fun i j hij => by
  unfold Formalism.BasicNotions.DomWeight.natW
  exact Int.toNat_le_toNat (by have := l.anti hij; omega)

private theorem exponent_bound : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ ∃ Dn : ℕ, 0 < Dn ∧
          (∀ p : ℕ, p.Prime → p ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p) ∣ Dn) ∧
          Real.log Dn ≤ K0 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b := by
  refine ⟨0, fun CF _ => ⟨100, fun ε => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hch
  have hch' : ch.sc = ⟨1, CF, large₂.sc.b⟩ := hch
  have hsc : ch.sc.cGap = 1 := by rw [hch']
  have hsize := hS.size
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSc, -, -⟩ := hS.size
  have hm2 := D.R.two_le_m
  have hga : 2 * bigN D ^ 3 + 2 * sLen D + 3 ≤ gap D 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN3 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have hNga : (bigN D : ℝ) + 3 ≤ (gap D 1 : ℝ) := by exact_mod_cast (by omega : bigN D + 3 ≤ gap D 1)
  have hm1 : (3 : ℝ) ≤ (D.R.m : ℝ) + 1 := by
    have : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
    linarith
  have hN0 : (0 : ℝ) ≤ (bigN D : ℝ) := Nat.cast_nonneg _
  have hγ3 : (3 : ℝ) ≤ (gap D 1 : ℝ) := by linarith
  have hmγ : (gap D 1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := le_mul_of_one_le_left (by linarith) (by linarith)
  have h9 : (3 : ℝ) * 3 ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := mul_le_mul hm1 hγ3 (by norm_num) (by linarith)
  have hScpos := large₂.Sc_pos
  have hb9 : 9 ≤ large₂.sc.b := by linarith
  have hbN : (bigN D : ℝ) ≤ large₂.sc.b := by linarith
  set b := large₂.sc.b with hb
  have hn : (ch.G.V (.top D.R.m)).rank = bigN D := rank_top ch.G
  set W : ℕ := ⌈8 * b⌉₊ with hW
  have hW1 : 8 * b ≤ (W : ℝ) := Nat.le_ceil _
  have hW2 : (W : ℝ) < 8 * b + 1 := Nat.ceil_lt_add_one (by linarith)
  have hnW : (ch.G.V (.top D.R.m)).rank - 1 ≤ W := by
    have h1 : ((ch.G.V (.top D.R.m)).rank : ℝ) ≤ W := by rw [hn]; linarith
    have h2 : (ch.G.V (.top D.R.m)).rank ≤ W := by exact_mod_cast h1
    omega
  have hwidth : ∀ (τ : D.what₂.Tau) (a : Fin (ch.G.V (.top D.R.m)).rank),
      (wt ch.G (.top D.R.m) τ).natW a + ((ch.G.V (.top D.R.m)).rank - 1 - a) ≤ W := by
    intro τ a
    exact natW_wtOf_add_le (ch.G.V (.top D.R.m)).rank
      (GlobalTheory.SignedHC.entries (Node.par D ch.sc.cGap (.top D.R.m) τ)) (-(6 * b)) (2 * b)
      (entries_top_bound D large₂ hsize τ _ hsc) W (by linarith) hnW a
  have hex : ∀ p : ℕ, p.Prime →
      (∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p) ≤
        (Fintype.card D.what₂.Tau * ((ch.G.V (.top D.R.m)).rank).choose 2) * Nat.log p W ∧
      (W < p → (∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p) = 0) := by
    intro p hp
    have hτ := fun τ => exZ_le_of_width _ (natW_anti' (wt ch.G (.top D.R.m) τ)) W (hwidth τ) p hp
    constructor
    · calc (∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p)
          ≤ ∑ _τ : D.what₂.Tau, ((ch.G.V (.top D.R.m)).rank).choose 2 * Nat.log p W :=
            Finset.sum_le_sum fun τ _ => (hτ τ).1
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_assoc]
    · intro hWp
      exact Finset.sum_eq_zero fun τ _ => (hτ τ).2 hWp
  obtain ⟨Dn, h0, hdvd, hlog⟩ := exists_prod_bound W _
    (fun p => ∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p) hex
  refine ⟨by linarith, Dn, h0, hdvd, ?_⟩
  have hA : ((Fintype.card D.what₂.Tau * ((ch.G.V (.top D.R.m)).rank).choose 2 : ℕ) : ℝ) ≤
      (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 := by
    have h1 : ((ch.G.V (.top D.R.m)).rank).choose 2 ≤ (ch.G.V (.top D.R.m)).rank ^ 2 := by
      rw [Nat.choose_two_right, sq]
      exact le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h2 : Fintype.card D.what₂.Tau * ((ch.G.V (.top D.R.m)).rank).choose 2 ≤ D.R.f * bigN D ^ 2 := by
      rw [D.what₂.card_Tau, ← hn]
      exact Nat.mul_le_mul_left _ h1
    exact_mod_cast h2
  have hWb : (W : ℝ) ≤ 9 * b := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hlogW : Real.log W ≤ 2 * Real.log b := by
    have h1 : Real.log W ≤ Real.log (9 * b) := Real.log_le_log hW0 hWb
    have h2 : Real.log (9 * b) = Real.log 9 + Real.log b := Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log 9 ≤ Real.log b := Real.log_le_log (by norm_num) hb9
    linarith
  have hlogW0 : 0 ≤ Real.log W := Real.log_natCast_nonneg W
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hP : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 := by positivity
  have s1 : ((Fintype.card D.what₂.Tau * ((ch.G.V (.top D.R.m)).rank).choose 2 : ℕ) : ℝ) * W ≤
      ((D.R.f : ℝ) * (bigN D : ℝ) ^ 2) * (9 * b) :=
    mul_le_mul hA hWb (Nat.cast_nonneg _) hP
  have s2 := mul_le_mul s1 hlogW hlogW0 (mul_nonneg hP (by linarith))
  have hQ : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * b * Real.log b := mul_nonneg (mul_nonneg hP (by linarith)) hlogb
  calc Real.log Dn ≤ _ := hlog
    _ ≤ _ := s2
    _ = 18 * ((D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * b * Real.log b) := by ring
    _ ≤ 100 * ((D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * b * Real.log b) := by linarith
    _ = 100 * (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * b * Real.log b := by ring

end GlobalTheory.FinSize

end

theorem _root_.GlobalTheory.T.exists_totalExponent_topWeight_bound : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ ∃ Dn : ℕ, 0 < Dn ∧
          (∀ p : ℕ, p.Prime → p ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p) ∣ Dn) ∧
          Real.log Dn ≤ K0 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b :=
  GlobalTheory.FinSize.exponent_bound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingExtendScalarsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem funEquiv_symm_mapVV {K ι : Type} [Field K] [CharZero K] [Fintype ι] {n : ℕ} (φ : K →+* ℂ)
    (σ : ι → DomWeight n) (v : VV K fun τ => (σ τ).dual) :
    (GlobalTheory.FunObj.funEquiv σ).symm (GlobalTheory.CoefModel.mapVV φ (fun τ => (σ τ).dual) v) =
      GlobalTheory.CoefModel.mapVV φ σ ((GlobalTheory.FunObj.funEquiv σ).symm v) := by
  have h1 : IsFunForm σ ((funEquiv σ).symm v) v := by
    have := isFunForm_funEquiv σ ((funEquiv σ).symm v)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h2 := GlobalTheory.BrRat.isFunForm_map φ σ h1
  have h3 := (isFunForm_iff_eq σ _ _).1 h2
  rw [LinearEquiv.symm_apply_eq]
  exact h3

theorem _root_.GlobalTheory.T.branchingPairing_extendScalars : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] {n N : ℕ} (φ : K →+* ℂ) (σ : ι → DomWeight n) (hN : N = n + 1)
    (Λ : ι → DomWeight N) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    GlobalTheory.FunObj.brPair σ hN Λ (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ (fun τ => (σ τ).dual) v) =
      φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro K ι _ _ _ n N φ σ hN Λ u v
  rw [brPair, LinearMap.compl₁₂_apply, pairBK_apply, pairB_apply, GlobalTheory.BrPairF.brPairF_apply, pairBK_apply, pairB_apply,
    GlobalTheory.BrRat.covOf_eq, funEquiv_symm_mapVV, GlobalTheory.CoefModel.mapVV_coe, Formalism.L2.Col.Br.brStd, LinearMap.comp_apply,
    Submodule.subtype_apply, Formalism.L2.Col.Br.brStd, LinearMap.comp_apply, Submodule.subtype_apply, GlobalTheory.CoefModel.mapVV_coe,
    GlobalTheory.Proof.TensorMapDescent.branchingProjection_map, GlobalTheory.Proof.TensorMapDescent.fockB_map, map_mul, map_inv₀]
  congr 2
  unfold extNormB
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeVertexLatticeGridCorner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem isLattice_comap_gl {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : Type} [Fintype n] [DecidableEq n]
    (g : GL n K) (M : Submodule R (n → K)) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (M.comap (g.1.mulVecLin.restrictScalars R)) := by
  let e : (n → K) ≃ₗ[K] (n → K) := LinearEquiv.ofLinear g.1.mulVecLin (g⁻¹).1.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])
  have h : M.comap (g.1.mulVecLin.restrictScalars R) = M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      have : e (e.symm y) ∈ M := by rw [e.apply_symm_apply]; exact hy
      exact this
  rw [h]
  refine ⟨hM.fg.map _, ?_⟩
  have h2 : ((M.map ((e.symm : (n → K) →ₗ[K] (n → K)).restrictScalars R) : Submodule R (n → K)) : Set (n → K)) =
      (e.symm : (n → K) →ₗ[K] (n → K)) '' (M : Set (n → K)) := rfl
  intro s hs hi
  rw [h2] at hs
  have hs' : e '' s ⊆ (M : Set (n → K)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hs hx
    simpa [← hyx] using hy
  have hi' : LinearIndepOn R id (e '' s) :=
    (linearIndepOn_id_imageₛ_iff (f := (e : (n → K) →ₗ[K] (n → K)).restrictScalars R)
      (show Function.Injective ((e : (n → K) →ₗ[K] (n → K)).restrictScalars R) from e.injective).injOn).2 hi
  have hk := hM.linearIndepOn (e '' s) hs' hi'
  have hk' := (linearIndepOn_id_imageₛ_iff (f := (e.symm : (n → K) →ₗ[K] (n → K)))
    (show Function.Injective (e.symm : (n → K) →ₗ[K] (n → K)) from e.symm.injective).injOn).2 hk
  change LinearIndepOn K id (e.symm '' (e '' s)) at hk'
  simpa [Set.image_image] using hk' 

theorem _root_.GlobalTheory.T.isLattice_vertexLattice_gridCorner : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)), Submodule.IsLattice D.host.E (GlobalTheory.SumSize.latAt S (.grid D.R.m D.R.m) y) := by
  intro D T L sc G W S y
  have hm := D.R.two_le_m
  have hΛ : Submodule.IsLattice D.host.E (G.Λ (.grid D.R.m D.R.m)) :=
    (G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
      have : D.R.m = 0 := (Node.grid.inj e).1
      omega).sd.1
  apply isLattice_comap_gl _ _
  apply Submodule.IsLattice.of_fg
  obtain ⟨c, hc, hu⟩ := Formalism.UG.P.adelstabL_upper (F := D.host.F) _ (Module.Finite.iff_fg.2 hΛ.fg)
  obtain ⟨d, hd, c', hc', hcg, hcgi⟩ := Formalism.UG.P.levelaf_exists_denom (E := D.host.E) (finG (G.V (.grid D.R.m D.R.m)) y)
  have hG := Formalism.UG.P.adelstab_entries (finG (G.V (.grid D.R.m D.R.m)) y) d c' hc' hcg
  exact Module.Finite.iff_fg.mp (Formalism.UG.P.adelstab_finite (finG (G.V (.grid D.R.m D.R.m)) y) _ c d hc hd hu hG)
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FPair

theorem bil {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W →ₗ[K] K) (s s' : K) (u : V) (v : W) : f (s • u) (s' • v) = s * (s' * f u v) := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private theorem full_grid_corner {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
    {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)) :
    Submodule.IsFullLattice D.host.E (latAt S (.grid D.R.m D.R.m) y) := by
  have hsd := (G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
    have : D.R.m = 0 := (Node.grid.inj e).1
    have := D.R.two_le_m
    omega).sd
  have hΛ := GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hsd
  have hglob := Formalism.UG.P.csGlob_lattice (F := D.host.F) _
    (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top (finG (G.V (.grid D.R.m D.R.m)) y)
  let g := S.N.fr (.grid D.R.m D.R.m)
  let e : (Fin (G.V (.grid D.R.m D.R.m)).rank → D.host.E) ≃ₗ[D.host.E]
      (Fin (G.V (.grid D.R.m D.R.m)).rank → D.host.E) := LinearEquiv.ofLinearMap g.1.mulVecLin (g⁻¹).1.mulVecLin
    (by rw [← Matrix.mulVecLin_mul, Units.mul_inv, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, Units.inv_mul, Matrix.mulVecLin_one])
  haveI : Submodule.IsLattice D.host.E (latAt S (.grid D.R.m D.R.m) y) :=
    GlobalTheory.T.isLattice_vertexLattice_gridCorner S y
  refine ⟨?_⟩
  have hset : (latAt S (.grid D.R.m D.R.m) y : Set _) =
      e.symm '' (Formalism.UG.CS.globLat (finG (G.V (.grid D.R.m D.R.m)) y) (G.Λ (.grid D.R.m D.R.m)) : Set _) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      change e (e.symm z) ∈ Formalism.UG.CS.globLat (finG (G.V (.grid D.R.m D.R.m)) y) (G.Λ (.grid D.R.m D.R.m))
      simpa using hz
  rw [hset, Submodule.span_image_linearEquiv, hglob.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem finPair : FinPairK := by
  obtain ⟨CF0, h6⟩ := GlobalTheory.T.exists_totalExponent_topWeight_bound
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨K0, h6'⟩ := h6 CF hCF
  refine ⟨max K0 0, fun ε C hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h6' ε
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ => ?_⟩
  obtain ⟨hb1, Dn, hDn, hdiv, hlog⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt
  obtain ⟨h5mul, h5div, h5fin, h5sum⟩ := GlobalTheory.T.placeValuation_localDegree_arithmetic (K := D.what₂.LL)
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (le_trans (by norm_num) hS.size.2.2.2.1 : 1 ≤ D.R.m)
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb1
  have hK : K0 ≤ C := (le_max_left _ _).trans hC
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  refine ⟨fun w => (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ), ⟨fun w => ?_, ?_, fun s => ?_⟩, ?_⟩
  · show (0 : ℝ) ≤ (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ)
    exact_mod_cast (h5div w Dn Dn hDn dvd_rfl).1
  · refine (h5fin Dn hDn).subset fun w hw => ?_
    intro h0
    exact hw (by simp [h0])
  · refine (h5sum Dn hDn s).trans (hlog.trans ?_)
    unfold bOne
    have e1 : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b := by positivity
    have e2 : K0 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b ≤
        C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b := by
      have := mul_le_mul_of_nonneg_right hK e1
      linarith
    have e3 : C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b ≤
        C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b := by
      have h1 : 0 ≤ C * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b := by positivity
      have h2 : Real.log large₂.sc.b ≤ D.R.m * (Real.log large₂.sc.b + sig ch.G) := by nlinarith
      have := mul_le_mul_of_nonneg_left h2 h1
      nlinarith
    exact e2.trans e3
  · intro w y a a' u v hu hv
    obtain ⟨u0, s, hu0, hs, hsa, hsu⟩ := hu
    obtain ⟨v0, s', hv0, hs', hsa', hsv⟩ := hv
    have hIS := fun τ => GlobalTheory.WtInterlace.weights_top_grid ch.G τ
    refine ⟨GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0, ?_, ?_⟩
    · rw [← hu0, ← hv0]
      exact (GlobalTheory.T.branchingPairing_extendScalars D.what₂.embLL _ _ _ u0 v0).symm
    · have h4 := GlobalTheory.T.branchingPairing_integral_upToExponents (labLL D) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) (listedWt ch.G (.grid D.R.m D.R.m))
        (fun τ => (hIS τ).1) (fun τ => (hIS τ).2) _ _ (full_grid_corner ch.S.toGridChoice y) (GlobalTheory.T.mem_vertexLatticeOrthonormalCoords_topNode_iff ch.S.toGridChoice y) w
        (s • u0) (s' • v0) hsu hsv
      erw [bil] at h4
      by_cases hy : GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0 = 0
      · exact Or.inl hy
      right
      rcases h4 with h0 | h4
      · exact absurd h0 (mul_ne_zero hs (mul_ne_zero hs' hy))
      rw [h5mul w _ _ hs (mul_ne_zero hs' hy), h5mul w _ _ hs' hy] at h4
      set p := Formalism.EigenvalueLevelCeiling.plc w
      set E := ∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p
      have hp := (h5div w (p ^ E) Dn hDn (hdiv p (Formalism.EigenvalueLevelCeiling.plc_prime w))).2
      rw [Nat.cast_pow] at hp
      have h4' : (-(Formalism.DivisionValues.vw w ((p : D.what₂.LL) ^ E) : ℝ)) ≤
          (Formalism.DivisionValues.vw w s : ℝ) + ((Formalism.DivisionValues.vw w s' : ℝ) + (Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0) : ℝ)) := by
        exact_mod_cast h4
      have hp' : (Formalism.DivisionValues.vw w ((p : D.what₂.LL) ^ E) : ℝ) ≤ (Formalism.DivisionValues.vw w ((Dn : ℕ) : D.what₂.LL) : ℝ) := by exact_mod_cast hp
      linarith

theorem infPair : InfPairK := by
  obtain ⟨CF0, h8⟩ := GlobalTheory.T.archimedean_branching_constant_bound
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨K0, h8'⟩ := h8 CF hCF
  refine ⟨max K0 0, fun ε C hC => ?_⟩
  obtain ⟨x₀, hx⟩ := h8' ε
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ => ?_⟩
  obtain ⟨hb1, hlog⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt
  have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hlb : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb1
  have hK : K0 ≤ C := (le_max_left _ _).trans hC
  have hC0 : 0 ≤ C := (le_max_right _ _).trans hC
  have hIS := fun τ => GlobalTheory.WtInterlace.weights_top_grid ch.G τ
  set P := ∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ) (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2 with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun τ _ => sq_nonneg _
  have hPa : P ≤ Real.exp (aOne ch.G C large₂.sc.b) := by
    have h1 : Real.log P ≤ aOne ch.G C large₂.sc.b := by
      refine hlog.trans ?_
      unfold aOne
      have e1 : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
      have e2 : 0 ≤ C * D.R.m * (bigN D : ℝ) ^ 2 * sig ch.G := by positivity
      have := mul_le_mul_of_nonneg_right hK e1
      nlinarith
    rcases hP0.lt_or_eq with h | h
    · calc P = Real.exp (Real.log P) := (Real.exp_log h).symm
        _ ≤ _ := Real.exp_le_exp.2 h1
    · rw [← h]; exact (Real.exp_pos _).le
  intro σ B B' u v hu hv
  obtain ⟨u0, hu0, hB⟩ := hu
  obtain ⟨v0, hv0, hB'⟩ := hv
  refine ⟨GlobalTheory.BrPairF.brPairF _ ch.G.sp.topDec.rank.symm _ u0 v0, ?_, ?_⟩
  · rw [← hu0, ← hv0]
    exact (GlobalTheory.T.branchingPairing_extendScalars D.what₂.embLL _ _ _ u0 v0).symm
  · obtain ⟨hn1, hn2, h7⟩ := GlobalTheory.T.branchingPairing_archimedean_bound_fockNorm σ ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) (listedWt ch.G (.grid D.R.m D.R.m))
      (fun τ => (hIS τ).1) (fun τ => (hIS τ).2) u0 v0
    refine h7.trans ?_
    have hB1 : (pairK (wt ch.G (.top D.R.m)) (fun _ => (1 : Matrix _ _ ℂ)) (GlobalTheory.CoefModel.mapVV σ _ u0)
        (GlobalTheory.CoefModel.mapVV σ _ u0)).re ≤ B := hB
    have hB2 : (pairK (fun τ => (listedWt ch.G (.grid D.R.m D.R.m) τ).dual) (fun _ => (1 : Matrix _ _ ℂ))
        (GlobalTheory.CoefModel.mapVV σ _ v0) (GlobalTheory.CoefModel.mapVV σ _ v0)).re ≤ B' := hB'
    have hPa' : (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank.symm.symm (wt ch.G (.top D.R.m) τ)
        (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ Real.exp (aOne ch.G C large₂.sc.b) := hPa
    have hP0' : 0 ≤ (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank.symm.symm (wt ch.G (.top D.R.m) τ)
        (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) := hP0
    have hBn : 0 ≤ B := hn1.trans hB1
    calc _ ≤ Real.exp (aOne ch.G C large₂.sc.b) * _ * _ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPa' hn1) hn2
      _ ≤ Real.exp (aOne ch.G C large₂.sc.b) * B * B' := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hB1 (Real.exp_pos _).le) hB2 hn2
          exact mul_nonneg (Real.exp_pos _).le hBn

end GlobalTheory.FPair

end
