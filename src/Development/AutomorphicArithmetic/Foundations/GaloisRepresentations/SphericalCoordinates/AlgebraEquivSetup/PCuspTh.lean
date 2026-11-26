module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
public import Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.TameLpOfCharIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.InIdBasic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCuspTh
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pCuspTh :
    CuspTh := by
  intro E _ _ _ n w σ
  let σ' : SmIrr (GLw n w) :=
    { V := σ.V
      ρ := σ.ρ.comp (invT n (w.adicCompletion E))
      smooth := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isSmooth_comp_invT σ.smooth
      irred := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isIrreducible_comp_invT σ.irred }
  refine ⟨σ', LinearEquiv.refl ℂ _, fun g g' v h => ?_, fun hc => ?_⟩
  · have hg : g' = invT n (w.adicCompletion E) g := Units.ext h
    subst hg
    show σ.ρ (invT n _ (invT n _ g)) v = σ.ρ g v
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT']
  · have h2 := PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing.WhittakerInverseTranspose.isCuspidal_comp_invT (ρ := σ'.ρ) hc
    have h3 : σ'.ρ.comp (invT n (w.adicCompletion E)) = σ.ρ :=
      MonoidHom.ext fun g => by
        show σ.ρ (invT n _ (invT n _ g)) = σ.ρ g
        rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT']
    rwa [h3] at h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFacEq
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pFacEq :
    FacEq := by
  intro E _ _ _ A n p _ S F hc w
  have h1 : IsFac F w (fac F.tr hc w) := by
    refine ⟨fun g => ?_, fun y => ?_⟩
    · have e : F.tr.j (F.tr.sec (F.tr.j g)) = F.tr.j g := F.tr.j_sec _
      have := (F.tr.j_eq _ _).1 e w.1 w.2.2
      rw [F.j_tr]
      exact this
    · rw [F.j_tr]
      rfl
  refine ⟨h1, fun L hL => ?_⟩
  have hpr : L.pr = (fac F.tr hc w).pr := MonoidHom.ext fun h => by
    obtain ⟨g, rfl⟩ := F.surj h
    rw [hL.1 g, h1.1 g]
  have hloc : L.loc = (fac F.tr hc w).loc := MonoidHom.ext fun y => by
    rw [hL.2 y, h1.2 y]
  cases hf : fac F.tr hc w with
  | mk pr loc pr_loc comm =>
    cases L with
    | mk pr' loc' pr_loc' comm' =>
      rw [hf] at hpr hloc
      simp only at hpr hloc
      subst hpr hloc
      rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongConj
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem comp_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := congrArg (RingHom.mapMatrix (pLoc E u)) (mem_Sim.1 k.2)
  rw [map_mul] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

theorem UpperTheory.Gal.W2.Seed.pCongConj :
    UpperTheory.Gal.CertificateRingHomMap.LocComm → CongConj := by
  intro _ E _ _ _ n N w g hs hc i k
  have hrel := comp_rel g w
  rw [hs, Units.val_one, map_one, map_one, one_smul] at hrel
  have hG : ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ = ((comp w g)⁻¹).val := by
    calc ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ
        = ((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ * ((comp w g).val * ((comp w g)⁻¹).val) := by
          rw [Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hrel, Matrix.one_mul]
  have hv := (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2
  have hent : conjLoc (GlobalTheory.SplitPts.conjE E) w (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k) = (((comp w g)⁻¹).val - 1) k i := by
    rw [← hG]
    by_cases hik : i = k
    · subst hik; simp [Matrix.sub_apply]
    · simp [Matrix.sub_apply, Matrix.one_apply, hik, Ne.symm hik]
  calc Valued.v (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k)
      = Valued.v (conjLoc (GlobalTheory.SplitPts.conjE E) w (((comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g).val - 1) i k)) := (hv _).symm
    _ = Valued.v ((((comp w g)⁻¹).val - 1) k i) := by rw [hent]
    _ ≤ Valued.v (N : w.adicCompletion E) := hc k i
    _ = Valued.v (conjLoc (GlobalTheory.SplitPts.conjE E) w (N : (UpperTheory.Gal.CertificateRingHomMap.cj w).adicCompletion E)) := by
          rw [map_natCast (conjLoc (GlobalTheory.SplitPts.conjE E) w) N]
    _ = Valued.v (N : (UpperTheory.Gal.CertificateRingHomMap.cj w).adicCompletion E) := hv _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNFact
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cong_conj_iff (hG : CongGrpEx) {E : Type} [Field E] [NumberField E] [IsCMField E] (n N : ℕ) (hN : 0 < N)
    (u : Plc E) (a : GLw n u) (ha : a ∈ GlobalTheory.LFun.KGL u (n := n)) (y : GLw n u) :
    (Cong1 N u (a * y * a⁻¹) ∧ Cong1 N u (a * y * a⁻¹)⁻¹) ↔ Cong1 N u y ∧ Cong1 N u y⁻¹ := by
  obtain ⟨K, hc, -, -, -, hn, -, -⟩ := hG E n N hN u
  rw [← hc, ← hc]
  exact hn a ha y

private theorem principalCongruence_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (N : ℕ) (u : Plc E) :
    Cong1 N u (1 : GLw n u) := by
  intro i k
  simp

theorem UpperTheory.Gal.W2.Seed.pKNFact :
    KNIff → FacEq → AtApart → CongGrpEx → CongConj → UpperTheory.Gal.W2.Seed.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocComm → KNFact := by
  intro hK _ _ hG hC _ hL E _ _ _ A n p _ S F w L hF q hq hgood hqw N hN K hKc
  have e : ∀ (u : Plc E) (g : GUf E n), GeneralLinearGroup.map (pLoc E u) (F.tr.a * mat g * F.tr.a⁻¹) =
      F.a u * comp u g * (F.a u)⁻¹ := by
    intro u g
    rw [F.a_tr]
    simp only [map_mul, map_inv]
    rfl
  have hCong : ∀ g : GUf E n, S.L.CongOne N (F.j g) ↔ ∀ u : Plc E, (p : 𝓞 E) ∉ u.asIdeal →
      Cong1 N u (F.a u * comp u g * (F.a u)⁻¹) := by
    intro g
    rw [F.j_tr, ((hK E A n p S F.tr g).2 N hN)]
    simp only [e]
  have einv : ∀ (u : Plc E) (g : GUf E n), F.a u * comp u g⁻¹ * (F.a u)⁻¹ = (F.a u * comp u g * (F.a u)⁻¹)⁻¹ := by
    intro u g
    rw [map_inv]
    group
  have hw := (hL E n w.1 w.2.1)
  have hcs : IsSplitAt (CertificateRingHomMap.cj w.1) := hw.2.2.2.1
  have hqc : (q : 𝓞 E) ∈ (CertificateRingHomMap.cj w.1).asIdeal := by
    by_contra hc
    haveI : Fact q.Prime := ⟨hq⟩
    have h1 : GlobalTheory.Cong.Apart w.1 (CertificateRingHomMap.cj w.1) := apart_of_not_mem (p := q) hc hqw
    exact (((hL E n (CertificateRingHomMap.cj w.1) hcs).2.1 w.1).1 h1).2 hw.2.2.2.2.1.symm
  have hcw := F.a_int w.1 q hq hgood hqw
  have hcc := F.a_int _ q hq hgood hqc
  have main : ∀ y : GLw n w.1, Cong1 N w.1 y → Cong1 N w.1 y⁻¹ → S.L.CongOne N (L.loc y) := by
    intro y h1 h2
    rw [hF.2, hCong]
    intro u _
    by_cases huw : u = w.1
    · subst huw
      rw [CertificateRingHomMap.comp_loc]
      exact ((cong_conj_iff hG n N hN _ _ hcw y).2 ⟨h1, h2⟩).1
    by_cases huc : u = CertificateRingHomMap.cj w.1
    · subst huc
      have c1 : Cong1 N (CertificateRingHomMap.cj w.1) (comp (CertificateRingHomMap.cj w.1) (CertificateRingHomMap.loc w.2.1 y)) :=
        hC E n N w.1 _ (CertificateRingHomMap.sim_loc _ _) (by rwa [CertificateRingHomMap.comp_loc])
      have c2 : Cong1 N (CertificateRingHomMap.cj w.1) (comp (CertificateRingHomMap.cj w.1) (CertificateRingHomMap.loc w.2.1 y))⁻¹ := by
        rw [← map_inv]
        exact hC E n N w.1 _ (by rw [map_inv, CertificateRingHomMap.sim_loc, inv_one]) (by rwa [map_inv, CertificateRingHomMap.comp_loc, inv_inv])
      exact ((cong_conj_iff hG n N hN _ _ hcc _).2 ⟨c1, c2⟩).1
    · rw [CertificateRingHomMap.comp_loc_of_apart w.2.1 (((hw.2.1 u).2 ⟨huw, huc⟩)) y]
      simpa using principalCongruence_one N u
  refine ⟨fun y hy => ?_, fun k hk => ?_⟩
  · obtain ⟨h1, h2⟩ := (hKc y).1 hy
    refine ⟨main y h1 h2, ?_⟩
    rw [← map_inv]
    exact main y⁻¹ h2 (by rwa [inv_inv])
  · obtain ⟨g, rfl⟩ := F.surj k
    rw [hF.1, hKc]
    have h1 := (hCong g).1 hk.1 w.1 w.2.2
    have h2 := (hCong g⁻¹).1 (by rw [map_inv]; exact hk.2) w.1 w.2.2
    rw [einv] at h2
    exact (cong_conj_iff hG n N hN _ _ hcw _).1 ⟨h1, h2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCongGrpEx
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem vN_le_one (N : ℕ) (w : Plc E) : Valued.v (N : w.adicCompletion E) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (natCast_mem (w.adicCompletionIntegers E) N)

private theorem vN_ne_zero {N : ℕ} (hN : 0 < N) (w : Plc E) : Valued.v (N : w.adicCompletion E) ≠ 0 := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  exact (Valuation.ne_zero_iff _).2 (Nat.cast_ne_zero.2 hN.ne')

private theorem vN_lt_one {N : ℕ} (w : Plc E) (h : (N : 𝓞 E) ∈ w.asIdeal) :
    Valued.v (N : w.adicCompletion E) < 1 := by
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) ((N : 𝓞 E) : E)) = w.valuation E ((N : 𝓞 E) : E) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have h2 : algebraMap E (w.adicCompletion E) ((N : 𝓞 E) : E) = (N : w.adicCompletion E) := by simp
  rw [← h2, h1]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 h

private theorem entry_mul_le {w : Plc E} {A B : Matrix (Fin n) (Fin n) (w.adicCompletion E)}
    {r s : WithZero (Multiplicative ℤ)} (hA : ∀ i j, Valued.v (A i j) ≤ r) (hB : ∀ i j, Valued.v (B i j) ≤ s)
    (i j : Fin n) : Valued.v ((A * B) i j) ≤ r * s := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hA _ _) (hB _ _)

private theorem cong_one (N : ℕ) (w : Plc E) : Cong1 N w (1 : GL (Fin n) (w.adicCompletion E)) := fun i k => by
  simp

private theorem cong_mul {N : ℕ} {w : Plc E} {x y : GL (Fin n) (w.adicCompletion E)}
    (hx : Cong1 N w x) (hy : Cong1 N w y) : Cong1 N w (x * y) := fun i k => by
  have e : (x * y).val - 1 = (x.val - 1) * (y.val - 1) + (x.val - 1) + (y.val - 1) := by
    rw [Units.val_mul]; noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  have h := vN_le_one (E := E) N w
  refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (hx i k)) (hy i k)
  exact (entry_mul_le hx hy i k).trans (mul_le_of_le_one_left' h)

private theorem cong_conj {N : ℕ} {w : Plc E} {a y : GL (Fin n) (w.adicCompletion E)}
    (ha : a ∈ KGL w (n := n)) (hy : Cong1 N w y) : Cong1 N w (a * y * a⁻¹) := fun i k => by
  have e : (a * y * a⁻¹).val - 1 = a.val * (y.val - 1) * (a⁻¹).val := by
    have h : a.val * (a⁻¹).val = 1 := by rw [← Units.val_mul]; simp
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, h]
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 ha
  have h1' : ∀ i j, Valued.v (a.val i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (h1 i j)
  have h2' : ∀ i j, Valued.v ((a⁻¹).val i j) ≤ 1 := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 (h2 i j)
  rw [e]
  simpa using entry_mul_le (entry_mul_le h1' hy) h2' i k

private theorem cong_entry {N : ℕ} {w : Plc E} {y : GL (Fin n) (w.adicCompletion E)} (hy : Cong1 N w y) (i j : Fin n) :
    Valued.v (y.val i j) ≤ max (Valued.v (N : w.adicCompletion E)) (Valued.v ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) := by
  have e : y.val i j = (y.val - 1) i j + (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by simp
  rw [e]
  exact (Valuation.map_add _ _ _).trans (max_le_max_right _ (hy i j))

private theorem cong_int {N : ℕ} {w : Plc E} {y : GL (Fin n) (w.adicCompletion E)} (hy : Cong1 N w y) (i j : Fin n) :
    y.val i j ∈ w.adicCompletionIntegers E := by
  refine (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 ((cong_entry hy i j).trans (max_le (vN_le_one N w) ?_))
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h]; simp

private def congGrp (N : ℕ) (w : Plc E) : Subgroup (GL (Fin n) (w.adicCompletion E)) where
  carrier := {y | Cong1 N w y ∧ Cong1 N w y⁻¹}
  one_mem' := ⟨cong_one N w, by simpa using cong_one N w⟩
  mul_mem' := fun {x y} hx hy => ⟨cong_mul hx.1 hy.1, by rw [_root_.mul_inv_rev]; exact cong_mul hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by simpa using hx.1⟩

private theorem isOpen_ball {w : Plc E} {c : w.adicCompletion E} (hc : c ≠ 0) :
    IsOpen {x : w.adicCompletion E | Valued.v x ≤ Valued.v c} := by
  have h0 : IsOpen ((w.adicCompletionIntegers E : Set (w.adicCompletion E))) :=
    Valued.isOpen_valuationSubring _
  have h1 : {x : w.adicCompletion E | Valued.v x ≤ Valued.v c} =
      (fun x => c⁻¹ * x) ⁻¹' (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
    ext x
    have hv : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w,
      map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 hv), mul_one]
  rw [h1]
  exact h0.preimage (continuous_const.mul continuous_id)

private theorem isOpen_cong {N : ℕ} (hN : 0 < N) (w : Plc E) :
    IsOpen {y : GL (Fin n) (w.adicCompletion E) | Cong1 N w y} := by
  have hc : (N : w.adicCompletion E) ≠ 0 := fun h => vN_ne_zero hN w (by rw [h, map_zero])
  have e : {y : GL (Fin n) (w.adicCompletion E) | Cong1 N w y} =
      ⋂ i, ⋂ k, (fun y : GL (Fin n) (w.adicCompletion E) => (y.val - 1) i k) ⁻¹'
        {x | Valued.v x ≤ Valued.v (N : w.adicCompletion E)} := by
    ext y
    simp [Cong1]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => (isOpen_ball hc).preimage ?_
  exact ((Units.continuous_val.sub continuous_const).matrix_elem i k)

private theorem isOpen_congGrp {N : ℕ} (hN : 0 < N) (w : Plc E) :
    IsOpen (congGrp (n := n) N w : Set (GL (Fin n) (w.adicCompletion E))) :=
  (isOpen_cong hN w).inter ((isOpen_cong hN w).preimage continuous_inv)

private theorem congGrp_le (N : ℕ) (w : Plc E) : congGrp (n := n) N w ≤ KGL w (n := n) := fun _ hy =>
  GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨cong_int hy.1, cong_int hy.2⟩

private theorem congGrp_le_iw {N : ℕ} (w : Plc E) (hN : (N : 𝓞 E) ∈ w.asIdeal) : congGrp (n := n) N w ≤ Iw n w := by
  intro y hy
  have hK : y ∈ GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion]
    exact congGrp_le N w hy
  refine GlobalTheory.SmGL.mem_iwahori.2 ⟨hK, fun i j hij => ?_⟩
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one]
  have h0 : (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0 := Matrix.one_apply_ne hij.ne'
  refine (cong_entry hy.1 i j).trans_lt (max_lt (vN_lt_one w hN) ?_)
  simp [h0]

theorem pCongGrpEx : CongGrpEx := by
  intro E _ _ _ n N hN w
  refine ⟨congGrp N w, fun y => Iff.rfl, isOpen_congGrp hN w, ?_, congGrp_le N w, ?_, fun h => congGrp_le_iw w h,
    fun y hy => ?_⟩
  · exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen _ (isOpen_congGrp hN w)) (congGrp_le N w)
  · intro a ha y
    have key : ∀ a ∈ KGL w (n := n), ∀ y, y ∈ congGrp N w → a * y * a⁻¹ ∈ congGrp N w := fun a ha y hy =>
      ⟨cong_conj ha hy.1, by
        have : (a * y * a⁻¹)⁻¹ = a * y⁻¹ * a⁻¹ := by group
        rw [this]; exact cong_conj ha hy.2⟩
    refine ⟨fun h => ?_, key a ha y⟩
    have := key a⁻¹ (inv_mem ha) _ h
    simpa [mul_assoc] using this
  · have := GlobalTheory.SmGL.iwahori_le_KO _ _ hy
    rwa [GlobalTheory.SmGL.SphCompletion.KO_completion] at this

end UpperTheory.Gal.W2.Seed
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLevSec
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pLevSec :
    UpperTheory.Gal.W2.Seed.IntConj → LevSec := by
  intro hIC E _ _ _ A n p _ S T S₀ Kw hS
  have hn : 0 < n := S.facts.pos
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 E)
  let w₀ : Plc E := ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
  have hsim : ∀ g : GUf E n, (∀ u, comp u g ∈ GlobalTheory.LFun.KGL u (n := n)) → sim g ∈ UpperTheory.Gal.CertificateRingHomMap.ZU :=
    fun g h => (hIC E n g w₀ hn).2.1 h
  have hcj : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → (p : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := by
    intro w hw
    have h1 : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      show algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
      simpa using hw
    rw [← GlobalTheory.LocInj.under_conjSrc w] at h1
    have h2 : algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := h1
    simpa using h2
  refine ⟨fun k hk => ?_, fun k h1 h2 _ => ?_⟩
  · obtain ⟨hs, hK, hR⟩ := UpperTheory.Gal.CertificateRingHomMap.mem_lev.1 hk
    have hoff : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w (T.sec (T.j k)) = comp w k :=
      (T.j_eq _ _).1 (T.j_sec _)
    have hover : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ GlobalTheory.LFun.KGL w (n := n) := fun w hw =>
      hR w (fun h => hS w h hw) (fun h => hS _ h (hcj w hw))
    have hq : sim ((T.sec (T.j k))⁻¹ * k) ∈ UpperTheory.Gal.CertificateRingHomMap.ZU := by
      refine hsim _ fun u => ?_
      rw [map_mul, map_inv]
      by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
      · rw [T.sec_p _ u hu, inv_one, one_mul]
        exact hover u hu
      · rw [hoff u hu, inv_mul_cancel]
        exact one_mem _
    refine UpperTheory.Gal.CertificateRingHomMap.mem_lev.2 ⟨?_, fun w hw => ?_, fun w hw hcw => ?_⟩
    · have e : sim (T.sec (T.j k)) = sim k * (sim ((T.sec (T.j k))⁻¹ * k))⁻¹ := by
        rw [map_mul, map_inv]; simp
      rw [e]
      exact mul_mem hs (inv_mem hq)
    · rw [hoff w (hS w hw)]
      exact hK w hw
    · by_cases hu : (p : 𝓞 E) ∈ w.asIdeal
      · rw [T.sec_p _ w hu]
        exact one_mem _
      · rw [hoff w hu]
        exact hR w hw hcw
  · have hall : ∀ u, comp u k ∈ GlobalTheory.LFun.KGL u (n := n) := fun u => by
      by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
      · exact h2 u hu
      · rw [h1 u hu]; exact one_mem _
    refine UpperTheory.Gal.CertificateRingHomMap.mem_lev.2 ⟨hsim k hall, fun w hw => ?_, fun w _ _ => hall w⟩
    rw [h1 w (hS w hw)]
    exact one_mem _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPhiTy
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pPhiTy :
    PPart → LevSec → FacEq → UpperTheory.Gal.W2.Seed.LocComm → PhiTy := by
  intro hP hL hF hc E _ _ _ A n p _ S F x U w₀ Up V _ _ _ hOff _ r W hAux N hN hStab L hw Ty hTy
  have hj : F.j = F.tr.j := F.j_tr
  have h4 : ∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) →
      (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ GlobalTheory.LFun.KGL w (n := n)) →
      ∀ g, V.Φ (CertificateRingHomMap.th (g * k)) = V.Φ (CertificateRingHomMap.th g) := by
    intro k h1 h2 g
    have hk : CertificateRingHomMap.th k ∈ lev V.S V.Kw :=
      (hL E A n p S F.tr V.S V.Kw hOff.1).2 _
        (fun w hw' => by rw [CertificateRingHomMap.comp_th, h1 w hw', map_one])
        (fun w hw' => by rw [CertificateRingHomMap.comp_th]; exact CertificateRingHomMap.invT_mem_KGL (h2 w hw'))
        (fun u _ => one_mem _)
    have e : comp w₀ (CertificateRingHomMap.th k) = 1 := by rw [CertificateRingHomMap.comp_th, h1 _ hw.2, map_one]
    have hJ : comp w₀ (CertificateRingHomMap.th k) ∈ V.J := e ▸ one_mem _
    have hχ : V.χ ⟨comp w₀ (CertificateRingHomMap.th k), hJ⟩ = 1 := by
      have : (⟨comp w₀ (CertificateRingHomMap.th k), hJ⟩ : V.J) = 1 := Subtype.ext e
      rw [this, map_one]
    rw [map_mul, V.form.right _ hk hJ, hχ]
    simp
  have h3 : ∀ g : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g ∈ GlobalTheory.LFun.KGL w (n := n)) →
      V.Φ (CertificateRingHomMap.th (F.tr.sec (F.j g))) = V.Φ (CertificateRingHomMap.th g) := by
    intro g hg
    obtain ⟨k, e, k1, k2, -⟩ := hP E A n p S F.tr g
    have := h4 k k1 (fun w hw' => by rw [k2 w hw']; exact hg w hw') (F.tr.sec (F.tr.j g))
    rw [← e] at this
    rw [hj]
    exact this.symm
  refine ⟨?_, ?_, h3, h4⟩
  · obtain ⟨g₀, h0, hg⟩ := hOff.2
    intro hz
    apply h0
    have e := congrFun hz (F.j (CertificateRingHomMap.th g₀))
    have e' : V.Φ (CertificateRingHomMap.th (F.tr.sec (F.j (CertificateRingHomMap.th g₀)))) = 0 := e
    rw [h3 _ (fun w hw' => by rw [CertificateRingHomMap.comp_th]; exact CertificateRingHomMap.invT_mem_KGL (hg w hw')), CertificateRingHomMap.th_th] at e'
    exact e'
  · intro k hk g
    obtain ⟨⟨k', e, hk'⟩, -⟩ := (hTy.K_iff k).1 hk
    rw [th_eq] at hk'
    have hs : F.tr.sec k ∈ lev V.S (CertificateRingHomMap.levT V.Kw) := by
      have := (hL E A n p S F.tr V.S (CertificateRingHomMap.levT V.Kw) hOff.1).1 k' (CertificateRingHomMap.th_mem_lev.1 hk')
      rwa [← hj, e] at this
    have hs' := CertificateRingHomMap.th_mem_lev.2 hs
    have hpr : Ty.L.pr k = comp w₀ (F.tr.sec k) := by
      have h := (hF E A n p S F hc ⟨w₀, hw⟩).2 _ (hTy.fac ⟨w₀, hw⟩)
      rw [hTy.L_eq, h]
      rfl
    have hyy : (comp w₀ (CertificateRingHomMap.th (F.tr.sec k))).val = ((Ty.L.pr k)⁻¹).valᵀ := by
      rw [CertificateRingHomMap.comp_th, CertificateRingHomMap.invT_val, hpr]
    have hyJ : Ty.L.pr k ∈ Ty.J := Ty.fact.2 k hk
    have hJ' : comp w₀ (CertificateRingHomMap.th (F.tr.sec k)) ∈ V.J := (hTy.J_iff _ _ hyy).1 hyJ
    show V.Φ (CertificateRingHomMap.th (F.tr.sec (g * k))) = ((Ty.ψ ⟨Ty.L.pr k, Ty.fact.2 k hk⟩ : ℂˣ) : ℂ) • V.Φ (CertificateRingHomMap.th (F.tr.sec g))
    rw [map_mul, map_mul, V.form.right _ hs' hJ', hTy.ψ_eq ⟨_, hyJ⟩ ⟨_, hJ'⟩ hyy]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSiteFact
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PInIdBasic
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.Int.Geo.Pl

section

variable {E : Type} [Field E] [NumberField E] (w : Plc E)

private theorem valued_algebraMap_adicCompletionIntegers_eq_intValuation (r : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) r : w.adicCompletionIntegers E) :
      w.adicCompletion E) = w.intValuation r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E) w r]
  exact HeightOneSpectrum.adicCompletion.valued_coe _ _ _

theorem inId_iff_le (𝔟 : Ideal (𝓞 E)) (y : w.adicCompletion E) : InId w 𝔟 y ↔ ∃ x ∈ 𝔟, Valued.v y ≤ w.intValuation x := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    change z ∈ Submodule.span _ _ at hz
    induction hz using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨x, hx, rfl⟩ := ha
      exact ⟨x, hx, (valued_algebraMap_adicCompletionIntegers_eq_intValuation w x).le⟩
    | zero => exact ⟨0, 𝔟.zero_mem, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨x1, h1, e1⟩ := ha
      obtain ⟨x2, h2, e2⟩ := hb
      have hab : Valued.v (((a + b : w.adicCompletionIntegers E)) : w.adicCompletion E) ≤
          max (Valued.v (a : w.adicCompletion E)) (Valued.v (b : w.adicCompletion E)) :=
        Valuation.map_add Valued.v (a : w.adicCompletion E) (b : w.adicCompletion E)
      rcases le_total (w.intValuation x1) (w.intValuation x2) with h | h
      · exact ⟨x2, h2, hab.trans (max_le (e1.trans h) e2)⟩
      · exact ⟨x1, h1, hab.trans (max_le e1 (e2.trans h))⟩
    | smul c a _ ha =>
      obtain ⟨x, hx, e⟩ := ha
      refine ⟨x, hx, ?_⟩
      have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
      have hm : Valued.v (((c • a : w.adicCompletionIntegers E)) : w.adicCompletion E) =
          Valued.v (c : w.adicCompletion E) * Valued.v (a : w.adicCompletion E) :=
        Valuation.map_mul Valued.v (c : w.adicCompletion E) (a : w.adicCompletion E)
      rw [hm]
      exact (mul_le_of_le_one_left' hc).trans e
  · rintro ⟨x, hx, hle⟩
    have hy : y ∈ w.adicCompletionIntegers E :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hle.trans (w.intValuation_le_one x))
    by_cases h0 : w.intValuation x = 0
    · rw [h0, le_zero_iff, Valuation.zero_iff] at hle
      exact ⟨0, Ideal.zero_mem _, by simp [hle]⟩
    · set a : w.adicCompletionIntegers E := algebraMap (𝓞 E) (w.adicCompletionIntegers E) x with ha_def
      have ha : Valued.v (a : w.adicCompletion E) = w.intValuation x := valued_algebraMap_adicCompletionIntegers_eq_intValuation w x
      have ha0 : (a : w.adicCompletion E) ≠ 0 := by
        intro h
        apply h0
        rw [← ha, h, map_zero]
      have hq : y / (a : w.adicCompletion E) ∈ w.adicCompletionIntegers E := by
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, ha]
        exact div_le_one_of_le₀ hle zero_le'
      refine ⟨⟨_, hq⟩ * a, Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hx), ?_⟩
      simp only [MulMemClass.coe_mul]
      exact div_mul_cancel₀ y ha0

end

end UpperTheory.Gal.Int.Geo.Pl
end
end

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LFun (KGL)

private lemma natCast_mem_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (u : Plc E) (m : ℕ) (h : (m : 𝓞 E) ∈ u.asIdeal) :
    (m : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal := by
  have e : HeightOneSpectrum.under (𝓞 ℚ) (UpperTheory.Gal.CertificateRingHomMap.cj u) = HeightOneSpectrum.under (𝓞 ℚ) u :=
    GlobalTheory.DefU.ClassFin.under_conjSrc (F := ℚ) (E := E) _ (fun x => by simp) u
  have h2 : ((m : 𝓞 ℚ) ∈ (HeightOneSpectrum.under (𝓞 ℚ) (UpperTheory.Gal.CertificateRingHomMap.cj u)).asIdeal) ↔
      ((m : 𝓞 ℚ) ∈ (HeightOneSpectrum.under (𝓞 ℚ) u).asIdeal) := by rw [e]
  simpa [HeightOneSpectrum.under, Ideal.under_def, Ideal.mem_comap] using h2.2 (by simpa [HeightOneSpectrum.under, Ideal.under_def, Ideal.mem_comap] using h)

private lemma natCast_not_mem_of_coprime {E : Type} [Field E] [NumberField E] (u : Plc E) {q m : ℕ} (hm : m.Coprime q)
    (hq : (q : 𝓞 E) ∈ u.asIdeal) : (m : 𝓞 E) ∉ u.asIdeal := fun h => by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hm
  have h1 : ((a * (m : ℤ) + b * (q : ℤ) : ℤ) : 𝓞 E) = 1 := by rw [hab]; simp
  refine u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← h1]
  push_cast
  exact add_mem (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hq)

private lemma comp_cj_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (hI : UpperTheory.Gal.W2.Seed.IntConj) {n : ℕ} (g : GUf E n)
    (w : Plc E) (hs : sim g ∈ UpperTheory.Gal.CertificateRingHomMap.ZU) (h : comp w g ∈ KGL w (n := n)) :
    comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g ∈ KGL (UpperTheory.Gal.CertificateRingHomMap.cj w) (n := n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e : comp (UpperTheory.Gal.CertificateRingHomMap.cj w) g = 1 := Units.ext (Subsingleton.elim _ _)
    rw [e]
    exact one_mem _
  · exact (hI E n g w hn).1 hs h

private lemma inId_of_int {E : Type} [Field E] [NumberField E] (u : Plc E) {𝔟 : Ideal (𝓞 E)} {s : 𝓞 E} (hs : s ∈ 𝔟)
    (hu : s ∉ u.asIdeal) {y : u.adicCompletion E} (hy : y ∈ u.adicCompletionIntegers E) : InId u 𝔟 y := by
  refine (inId_iff_le u 𝔟 y).2 ⟨s, hs, ?_⟩
  have h1 : u.intValuation s = 1 :=
    le_antisymm (u.intValuation_le_one s) (not_lt.1 fun h => hu ((u.intValuation_lt_one_iff_mem s).1 h))
  rw [h1]
  exact hy

private lemma q_in_uId {p : ℕ} [Fact p.Prime] (D : Datum p) (q : ℕ) (r : ℤ) : (q : 𝓞 D.F) ∈ uId D q r :=
  Ideal.subset_span (by simp)

private lemma ω_in_uId {p : ℕ} [Fact p.Prime] (D : Datum p) (q : ℕ) (r : ℤ) : D.ω - (r : 𝓞 D.F) ∈ uId D q r :=
  Ideal.subset_span (by simp)

private lemma exists_not_mem_of_sup {E : Type} [Field E] [NumberField E] (w : Plc E) {𝔞 : Ideal (𝓞 E)} (h : 𝔞 ⊔ w.asIdeal = ⊤) :
    ∃ t ∈ 𝔞, t ∉ w.asIdeal := by
  by_contra hc
  push_neg at hc
  have h1 : 𝔞 ≤ w.asIdeal := hc
  rw [sup_eq_right.2 h1] at h
  exact w.isPrime.ne_top h

private lemma loc_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (hD : Dict) (hS : Sides) (hI : UpperTheory.Gal.W2.Seed.IntConj) (hC : UpperTheory.Gal.CertificateRingHomMap.LocComm) (F : Frame S) {x : E} (hx : Gen A x)
    {N : Lv p} {w : Plc E} (σ : Site S N w) (hw : IsSplitAt w) {y : GLw n w} (hy : y ∈ KGL w (n := n)) :
    F.j (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ σ.K₀ := by
  have hq : σ.q.Prime := σ.atp.prime
  have hG : A.Good σ.q := σ.good
  have hqw : (σ.q : 𝓞 E) ∈ w.asIdeal := σ.atp.le (q_in_uId S.D _ _)
  have hrw : A.ω - (σ.r : 𝓞 E) ∈ w.asIdeal := σ.atp.le (ω_in_uId S.D _ _)
  obtain ⟨-, hap, -, -, -, -⟩ := hC E n w hw
  have hqc : (σ.q : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := natCast_mem_cj w _ hqw
  obtain ⟨s1, -, -, -, -, -, s7⟩ := hS E A x hx σ.q hq hG.1 w hqw
  obtain ⟨-, hN, -, hsup, e, he⟩ := σ.lv
  have hω : (A.ω - (σ.r : 𝓞 E)) ^ e ∈ σ.𝔞 := he (Ideal.pow_mem_pow (ω_in_uId S.D _ _) e)
  have ht : ∃ t ∈ σ.𝔞, t ∉ w.asIdeal := exists_not_mem_of_sup w hsup
  have ht' : (A.ω - (σ.r : 𝓞 E)) ^ e ∉ (UpperTheory.Gal.CertificateRingHomMap.cj w).asIdeal := fun h =>
    s1 ((s7 σ.r hrw _).2 ⟨hqc, (UpperTheory.Gal.CertificateRingHomMap.cj w).isPrime.mem_of_pow_mem e h⟩)
  have hs : ∀ (u : Plc E) (t : 𝓞 E), (σ.q : 𝓞 E) ∈ u.asIdeal → t ∈ σ.𝔞 → t ∉ u.asIdeal →
      ∃ s ∈ Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞, s ∉ u.asIdeal := fun u t h1 h2 h3 =>
    ⟨_, Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) h2, fun h =>
      (u.isPrime.mem_or_mem h).elim (natCast_not_mem_of_coprime u hN h1) h3⟩
  have hb : Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞 ≠ ⊥ := by
    intro h
    have h1 : ((N.1 : ℕ) : 𝓞 E) ∈ Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞 := σ.mem
    rw [h, Ideal.mem_bot] at h1
    have h2 : N.1 = 0 := by exact_mod_cast h1
    have := N.2.1
    omega
  have hy' : comp w (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ KGL w (n := n) := by
    rwa [UpperTheory.Gal.CertificateRingHomMap.comp_loc]
  have tri : ∀ u : Plc E, comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) = 1 ∨ ((σ.q : 𝓞 E) ∈ u.asIdeal ∧
      comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ KGL u (n := n) ∧ ∃ s ∈ Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞, s ∉ u.asIdeal) := by
    intro u
    by_cases h1 : u = w
    · rw [h1]
      obtain ⟨t, h2, h3⟩ := ht
      exact Or.inr ⟨hqw, hy', hs _ t hqw h2 h3⟩
    by_cases h2 : u = UpperTheory.Gal.CertificateRingHomMap.cj w
    · rw [h2]
      exact Or.inr ⟨hqc, comp_cj_mem hI _ _ (by simp [one_mem]) hy', hs _ _ hqc hω ht'⟩
    · exact Or.inl (UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩) y)
  have hK : ∀ u : Plc E, (σ.q : 𝓞 E) ∈ u.asIdeal → comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) ∈ KGL u (n := n) →
      F.a u * comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) * (F.a u)⁻¹ ∈ KGL u (n := n) := fun u h1 h2 =>
    have ha := F.a_int u σ.q hq hG h1
    mul_mem (mul_mem ha h2) (inv_mem ha)
  refine (σ.isLev _).2 ⟨(hD E A n p S F _).2.1.2 fun u _ => ?_, ((hD E A n p S F _).2.2.1 _ hb).2 fun u _ i k => ?_⟩
  · rcases tri u with h | ⟨h1, h2, -⟩
    · simp [h, one_mem]
    · exact hK u h1 h2
  · rcases tri u with h | ⟨h1, h2, s, h3, h4⟩
    · have h0 : F.cmp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) = 1 := by simp [Frame.cmp, h]
      rw [h0]
      exact ⟨0, zero_mem _, by simp⟩
    · refine inId_of_int u h3 h4 ?_
      have hc := (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 (hK u h1 h2)).1 i k
      have hc' : F.cmp u (UpperTheory.Gal.CertificateRingHomMap.loc hw y) i k ∈ u.adicCompletionIntegers E := hc
      rw [Matrix.sub_apply, Matrix.one_apply]
      split_ifs
      · exact sub_mem hc' (one_mem _)
      · simpa using hc'

private lemma pr_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}
    (hD : Dict) (F : Frame S) {N : Lv p} {w : Plc E} (σ : Site S N w) (hp : (p : 𝓞 E) ∉ w.asIdeal) {g : GUf E n}
    (hk : F.j g ∈ σ.K₀) : comp w g ∈ KGL w (n := n) := by
  have h1 := ((σ.isLev _).1 hk).1
  have h2 := (hD E A n p S F g).2.1.1 h1 w hp
  have ha := F.a_int w σ.q σ.atp.prime σ.good (σ.atp.le (q_in_uId S.D _ _))
  have e : comp w g = (F.a w)⁻¹ * (F.a w * comp w g * (F.a w)⁻¹) * F.a w := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem ha) h2) ha

theorem UpperTheory.Gal.W2.Seed.pSiteFact :
    Dict → Sides → UpperTheory.Gal.W2.Seed.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → SiteFact := by
  intro hD hS hI hC E _ _ _ A n p _ S F x hx N w σ L hL
  refine ⟨fun y hy => ?_, fun k hk => ?_⟩
  · rw [hL.2 y]
    exact loc_mem hD hS hI hC F hx σ w.2.1 hy
  · obtain ⟨g, rfl⟩ := F.surj k
    rw [hL.1 g]
    exact pr_mem hD F σ w.2.2 hk
end
