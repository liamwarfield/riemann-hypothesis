module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.LocalToGlobal.GaloisLevelStructure.LinkChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwUnit

section Diag

variable {E : Type} [Field E]


open Classical in
def dEnt (n : ℕ) (π : E) (i : Fin n) : E := if i.1 + 1 = n then (if π = 0 then 1 else π) else 1

theorem dEnt_ne (n : ℕ) (π : E) (i : Fin n) : dEnt n π i ≠ 0 := by
  unfold dEnt
  split_ifs with h1 h2 <;> simp_all

def dAut (n : ℕ) (π : E) : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.piCongrRight fun i => LinearEquiv.smulOfNeZero E E (dEnt n π i) (dEnt_ne n π i)

theorem dAut_apply (n : ℕ) (π : E) (x : Fin n → E) (i : Fin n) : dAut n π x i = dEnt n π i * x i := rfl

end Diag

theorem exists_tw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (π : 𝓞 E), (∀ P ∈ Q, π ∉ P.asIdeal) → ∃ t : GL (Fin n) (AfE F E), t ∈ K1 hc n ST SG ∧ (∀ (P : Q) (i j : Fin n), adAt F P.1 (t.1 i j) = algebraMap E _ (if i = j then (if i.1 + 1 = n then (π : E) else 1) else 0)) ∧ ∀ w : HeightOneSpectrum (𝓞 E), w ∉ Q → conjPrime₂ w ∉ Q → ∀ i j : Fin n, adAt F w (t.1 i j) = if i = j then 1 else 0 := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ π hπ
  classical
  have hQc : ∀ P ∈ Q, conjPrime₂ P ∉ Q := fun P hP => (hQ P hP).2.2.2.2
  have hπ0 : ∀ P ∈ Q, (π : E) ≠ 0 := fun P hP h => hπ P hP (by
    have : π = 0 := RingOfIntegers.coe_eq_zero_iff.1 h
    rw [this]; exact P.asIdeal.zero_mem)
  have hval : ∀ P ∈ Q, ∀ i : Fin n, P.valuation E (dEnt n (π : E) i) = 1 := by
    intro P hP i
    unfold dEnt
    rw [if_neg (hπ0 P hP)]
    split_ifs
    · exact le_antisymm (HeightOneSpectrum.valuation_le_one _ π)
        (not_lt.1 fun h => hπ P hP ((HeightOneSpectrum.valuation_lt_one_iff_mem _ _).1 h))
    · exact map_one _
  have hfr : ∀ P ∈ Q, CharValCompare.IsFr P (Formalism.UG.CS.globLat (1 : GL (Fin n) (AfE F E)) (stdLat E n))
      (dAut n (π : E)) := by
    intro P hP x
    rw [globLat_one_std]
    show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n) ↔ x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)
    rw [mem_localization_standardLattice, mem_localization_standardLattice]
    simp only [dAut_apply, CharValCompare.intAt_iff, map_mul, hval P hP, one_mul]
  obtain ⟨g, hg, c1, c2, c3⟩ := PtExist.exists_modify (hc := hc) hQc (one_mem (UAd hc n)) (fun _ => dAut n (π : E)) hfr

  have hST : ∀ P ∈ ST, P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP =>
    ⟨fun h => (hQ P h).1 hP, fun h => (hQ _ h).2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hP)⟩
  have hSG : ∀ P ∈ SG, P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP =>
    ⟨fun h => (hQ P h).2.1 hP, fun h => (hQ _ h).2.2.2.1 (by rw [CharValCompare.conjP_conjP]; exact hP)⟩
  let p : DecoF E n ST SG ∅ :=
    ⟨(⟨decoRaw ST SG (1 : GL (Fin n) (AfE F E)),
      decorated_lattice_exists hc n ST SG 1 (one_mem _)⟩, fun P => Finset.notMem_empty _ P.2 |>.elim),
      fun P => Finset.notMem_empty _ P.2 |>.elim⟩
  have hb : IsPtOf hc 1 p := by
    apply (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ 1 p rfl).2
    exact ⟨one_mem _, rfl⟩
  have hpt : IsPtOf hc g p := by
    refine ⟨hg, ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P => absurd P.2 (Finset.notMem_empty _)⟩
    · exact c1
    · rw [c3 P.1 (hST P.1 P.2).1 (hST P.1 P.2).2 x i]
      exact hb.f P x hx i hi
    · rw [c3 w.1 (hSG w.1 w.2).1 (hSG w.1 w.2).2 x i]
      exact hb.be w x hx i
  have hd := (PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g p rfl).1 hpt
  have hK := mem_principal_of_same_decoration hc n ST SG (one_mem _) hg hd.2
  rw [inv_one, one_mul] at hK
  refine ⟨g, hK, fun P i j => ?_, fun w hw hw' i j => ?_⟩
  · rw [c2 P.1 P.2 i j]
    congr 1
    show dAut n (π : E) (Pi.single j 1) i = _
    rw [dAut_apply]
    unfold dEnt
    rw [if_neg (hπ0 P.1 P.2)]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  · have e1 : ∀ i j, adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        if i = j then 1 else 0 := by
      intro i j
      have h := c3 w hw hw' (Pi.single j 1) i
      have hv : (fun k => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((Pi.single j (1 : E) : Fin n → E) k)) =
          Pi.single j 1 := by
        ext k
        by_cases hk : k = j
        · subst hk; simp
        · simp [hk]
      have h' : adAt F w ((((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) =
          adAt F w ((((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ Pi.single j 1) i) := by
        rw [← hv]; exact h
      rw [inv_one, Units.val_one, Matrix.one_mulVec, Matrix.mulVec_single_one] at h'
      have h'' : adAt F w (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
          adAt F w ((Pi.single j 1 : Fin n → AfE F E) i) := h'
      rw [h'', Pi.single_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have hMi : (((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F w) = 1 := by
      ext a b
      rw [Matrix.map_apply, e1, Matrix.one_apply]
    have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)) * ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hM : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F w) = 1 := by
      have h := congrArg (fun M => M.map (adAt F w)) hgg
      simp only [Matrix.map_mul, hMi, mul_one] at h
      rw [h, Matrix.map_one _ (map_zero _) (map_one _)]
    have h := congrFun (congrFun hM i) j
    rw [Matrix.map_apply, Matrix.one_apply] at h
    exact h

end GlobalTheory.Mem.Col2.TwUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicTwistDiagonalAtPrimesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryAdelic_twist_diagonal_at_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (π : 𝓞 E), (∀ P ∈ Q, π ∉ P.asIdeal) → ∃ t : GL (Fin n) (AfE F E), t ∈ K1 hc n ST SG ∧ (∀ (P : Q) (i j : Fin n), adAt F P.1 (t.1 i j) = algebraMap E _ (if i = j then (if i.1 + 1 = n then (π : E) else 1) else 0)) ∧ ∀ w : HeightOneSpectrum (𝓞 E), w ∉ Q → conjPrime₂ w ∉ Q → ∀ i j : Fin n, adAt F w (t.1 i j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.Mem.Col2.TwUnit.exists_tw | exact GlobalTheory.Mem.Col2.TwUnit.exists_tw | (intros; apply GlobalTheory.Mem.Col2.TwUnit.exists_tw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondElementIntegralSupportLastRowStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondElement_integral_support_lastRow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (J : Matrix (Fin n) (Fin n) E) (S : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad) (π : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ) (δ : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)), J = 1 → P.under (𝓞 F) = v → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P) → π ∈ P.asIdeal → π ∉ P.asIdeal ^ 2 → π ∉ (conjPrime₂ P).asIdeal → (∀ x, x ∈ S.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = n → π ∣ r)) → (∀ t t' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J S.Lb)), t'.1 = inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0) → IsDia S v hv a δ → (∀ i j, δ.1.1 i j ∈ RInt F E) ∧ (∀ i j, (δ.1⁻¹).1 i j ∈ RInt F E) ∧ (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ≠ v → ∀ i j, adAt F w ((δ.1⁻¹).1 i j) = if i = j then 1 else 0) ∧ ∀ r j : Fin n, r.1 + 1 = n → HasRes P (adAt F P ((δ.1⁻¹).1 r j)) (if j = r then (a : 𝓞 E ⧸ P.asIdeal) else 0) := by
  first | exact @GlobalTheory.Mem.Dil.dia_data | exact GlobalTheory.Mem.Dil.dia_data | (intros; apply GlobalTheory.Mem.Dil.dia_data <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnCharts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.DiaChart

theorem normal_rep {G D A : Type} [Group G] [MulAction G D] (f : D → A) (pref : D → Prop)
    (h : ∀ q, pref q ↔ f q = Classical.epsilon (p := fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩))
    (d d' : D) (hd : ∀ g : G, f (g • d') = f (g • d)) :
    f (prefRep pref (Quotient.mk (MulAction.orbitRel G D) d')) = f (prefRep pref (Quotient.mk (MulAction.orbitRel G D) d)) := by
  have h1 : ∀ (q : D) (g₀ : G), (fun r => ∃ g : G, r = f (g • g₀ • q)) = fun r => ∃ g : G, r = f (g • q) := fun q g₀ => by
    funext r
    refine propext ⟨fun ⟨g, e⟩ => ⟨g * g₀, by rw [mul_smul]; exact e⟩, fun ⟨g, e⟩ => ⟨g * g₀⁻¹, by
      rw [mul_smul, inv_smul_smul]; exact e⟩⟩
  have h2 : ∀ q : D, f (prefRep pref (Quotient.mk (MulAction.orbitRel G D) q)) =
      Classical.epsilon (p := fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩) := fun q => by
    have hex : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = Quotient.mk (MulAction.orbitRel G D) q ∧ pref p := by
      obtain ⟨g, hg⟩ := Classical.epsilon_spec (p := fun r => ∃ g : G, r = f (g • q)) ⟨f q, 1, by rw [one_smul]⟩
      refine ⟨g • q, Quotient.sound ⟨g, rfl⟩, (h _).2 ?_⟩
      rw [h1]
      exact hg.symm
    unfold prefRep
    rw [dif_pos hex]
    obtain ⟨g, hg⟩ : ∃ g : G, g • q = hex.choose := Quotient.exact hex.choose_spec.1
    have h3 := (h _).1 hex.choose_spec.2
    rw [h3, ← hg, h1]
  rw [h2, h2]
  simp only [hd]

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

theorem mv_dia (q : PtAt R sel mu cst u j) (P : Pr.vT u) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    PtY.mv q (DecoSet.dia1 P a q.1.1.deco) = ⟨(⟨(DecoSet.dia1 P a q.1.1.deco, q.1.1.1.2), q.1.1.2⟩, q.1.2), q.2⟩ := by
  unfold PtY.mv
  exact dite_eq_left ⟨q.1.1.2, q.2⟩

theorem cosetIn_dia (q : PtAt R sel mu cst u j) (P : Pr.vT u) (a : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) :
    cosetIn (PtY.mv q (DecoSet.dia1 P a q.1.1.deco) : PtAt R sel mu cst u j) = cosetIn q := by
  rw [mv_dia]
  rfl

theorem cosetIn_of_ne (h : j + 1 ≠ R.m) (q : PtAt R sel mu cst u j) : cosetIn q = fun _ => ∅ := by
  have h2 : q.1.2 = ∅ := by
    have := q.2
    rw [ysAt_ys_of_ne sel mu cst h] at this
    exact this
  funext P
  unfold cosetIn
  rw [h2]
  simp

end Pt

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev dp (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (c : (I.stp u a i).Cl) :
    (I.stp u a i).D c.1 := PtY.mv ((I.stp u a i).rep c) (DecoSet.dia1 P s ((I.stp u a i).rep c).1.1.deco)

theorem cosetIn_rep (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ)
    (c : (I.stp u a i).Cl) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (dp I u a i P s c))) = cosetIn ((I.stp u a i).rep c) := by
  by_cases h : i + 1 = B.R.m
  · have h2 := @normal_rep ((I.stp0 u a i).G c.1) ((I.stp0 u a i).D c.1) _ _ ((I.stp0 u a i).actD c.1) (fun q => cosetIn q) (I.pref u a i c.1)
      (fun q => ⟨fun hq => hq.2.1 h, fun hq => ⟨fun h0 => by have := B.R.two_le_m; omega, fun _ => hq, fun h0 => by omega⟩⟩)
      ((I.stp u a i).rep c) (dp I u a i P s c) (fun g => by
        have e := ((l.lev u a).lev i).dia_act c.1 P s g ((I.stp u a i).rep c)
        exact (congrArg (fun q : (I.stp0 u a i).D c.1 => cosetIn q) e.symm).trans (cosetIn_dia _ P s))
    refine h2.trans ?_
    exact congrArg (fun q => cosetIn ((I.stp u a i).rp c.1 q)) ((I.stp u a i).rp_spec c.1 c.2)
  · rw [cosetIn_of_ne h, cosetIn_of_ne h]


set_option maxHeartbeats 1000000 in
theorem exists_level (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k : Ch → GA B (B.R.N i)}
    (h : I.Reads u a i chOf Lb U chi y st k) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (c : (I.stp u a i).Cl)
    (δ : GA B (B.R.N i)) (hδ : PtOf (y c * δ * k (chOf c)) (dp I u a i P s c).1.1) (β : Ch)
    (hβ : chOf ((I.stp u a i).cl c.1 (dp I u a i P s c)) = β) :
    ∃ x : U β, y c * δ = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
        ((I.stp u a i).gam c.1 ((I.stp u a i).mv c.1 (dp I u a i P s c))) * y ((I.stp u a i).cl c.1 (dp I u a i P s c)) * x.1 ∧
      ((chi β x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 ((I.stp u a i).mv c.1 (dp I u a i P s c)) : B.LLˣ) : B.LL) := by
  subst hβ
  have hch : chOf ((I.stp u a i).cl c.1 (dp I u a i P s c)) = chOf c := (h.key _ _).2 ⟨rfl, cosetIn_rep I l u a i P s c⟩
  have hg := (I.stp u a i).mv_smul c.1 (dp I u a i P s c)
  have hco := cosetIn_rep I l u a i P s c
  have hco' : cosetIn (dp I u a i P s c) = cosetIn ((I.stp u a i).rep c) := cosetIn_dia _ P s
  generalize (I.stp u a i).mv c.1 (dp I u a i P s c) = g at hg ⊢
  rw [← hch] at hδ
  have hlev := h.lev ((I.stp u a i).cl c.1 (dp I u a i P s c))
  have hchr := h.chr ((I.stp u a i).cl c.1 (dp I u a i P s c))
  generalize y ((I.stp u a i).cl c.1 (dp I u a i P s c)) = y' at hlev hchr ⊢
  obtain ⟨γ, κ⟩ := g
  have hk : (I.stp u a i).act c.1 (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl c.1 (dp I u a i P s c))) =
      (I.stp u a i).act c.1 (γ⁻¹, 1) (dp I u a i P s c) := by
    refine Eq.trans ?_ (congrArg ((I.stp u a i).act c.1 (γ⁻¹, 1)) hg)
    refine Eq.trans ?_ (((I.stp u a i).actD c.1).mul_smul (γ⁻¹, 1) (γ, κ) _)
    rw [Prod.mk_mul_mk, inv_mul_cancel, one_mul]
    rfl
  have hpt : PtOf (y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * (y c * δ))) * k (chOf ((I.stp u a i).cl c.1 (dp I u a i P s c))))
      ((I.stp u a i).act c.1 (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl c.1 (dp I u a i P s c)))).1.1 := by
    rw [hk, mul_inv_cancel_left, mul_assoc]
    exact GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ _ _ _ _ _ γ⁻¹ _ _ hδ
  have hx := (hlev _ _ hpt).2 ⟨(1, κ), map_one (ufGL _ _), rfl, by
    refine Eq.trans ?_ (hco'.trans hco.symm)
    refine (congrArg (fun q : (I.stp u a i).D c.1 => cosetIn q) hk).trans ?_
    exact GlobalTheory.T.couplingCoset_frames_invariant_rational_unitary _ _ _ _ _ _ _ _ _ (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr _ _ γ⁻¹ rfl rfl⟩
  refine ⟨⟨_, hx⟩, ?_, hchr ⟨_, hx⟩ (1, κ) (map_one (ufGL _ _)) hpt⟩
  show y c * δ = ratAd B.host.F γ * y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * (y c * δ)))
  rw [mul_assoc, mul_inv_cancel_left, ← mul_assoc]
  unfold ratAd
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, one_mul]


set_option maxHeartbeats 1000000 in
theorem isPt_dia (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k : Ch → GA B (B.R.N i)}
    (h : I.Reads u a i chOf Lb U chi y st k) (P : (B.primes X).vT u) (s : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) (c : (I.stp u a i).Cl)
    {f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {J : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E} (hJ : J = 1)
    (S : Formalism.L2.Forms.StepLevel B.host.F B.host.E B.sp.cm.sig J (B.T u) f bad) (hL : S.Lb = Lb (chOf c))
    (v : HeightOneSpectrum (𝓞 B.host.F)) (hv : (B.T u : 𝓞 B.host.F) ∈ v.asIdeal) (hP : v = P.1.under (𝓞 B.host.F))
    (hs : ∀ t t' : latS (F := B.host.F) (v.adicCompletion B.host.F) (intV B.host.E v)
        (Submodule.span (𝓞 B.host.E) (dualSet (B.sp.cm.sig : B.host.E →+* B.host.E) J S.Lb)),
      t'.1 = inclE (F := B.host.F) (v.adicCompletion B.host.F) ((X.piT u : 𝓞 B.host.E) : B.host.E) • t.1 → S.fT v hv t' = 0)
    (z : ℤ) (hz : (z : 𝓞 B.fields.E ⧸ P.1.asIdeal) = s) (δ : UPts B.sp.cm.sig J (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
    (hδ : IsDia S v hv z δ) : PtOf (y c * δ.1 * k (chOf c)) (dp I u a i P s c).1.1 := by
  classical
  have hX := FieldsLaws.fields_ok B
  have hPr := l.pr
  have hover : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w.under (𝓞 B.host.F) = v → w = P.1 ∨ w = conjPrime₂ P.1 := fun w hw =>
    (under_eq_iff B.host P.1 w).1 (hw.trans hP)
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.diamondElement_integral_support_lastRow _ _ B.sp.cm _ _ _ _ J S (X.piT u) P.1 v hv z δ hJ hP.symm hover
    (decoFin_mem_of_mem_divs P.2) (hPr.piT_notMem_sq hX u P.2) (conj_piT_notMem hPr u P)
    (fun x => by rw [hL]; exact h.lb _ x) hs hδ
  obtain ⟨p₀, hp₀, hN⟩ := h.k_std (chOf c)
  have hdis : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_left.2 fun w hw hw' => by
    obtain ⟨j, hj⟩ := exists_g_mem hPr ⟨w, hw⟩
    exact GlobalTheory.Proof.NarrowJetMoments.notMem_of_mem_QE hI.sel_ok hw' (hPr.g_prime j) (hI.g_mem j) hj
  have hT : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w.under (𝓞 B.host.F) = v → (B.T u : 𝓞 B.host.E) ∈ w.asIdeal := fun w hw => by
    rw [← hw] at hv
    have h1 : algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ w.asIdeal := hv
    rwa [map_natCast] at h1
  refine GlobalTheory.T.isPointOf_last_coordinate_dilation_one_prime _ _ B.sp.cm _ _ _ _ (y c) δ.1 (k (chOf c)) ((I.stp u a i).rep c).1.1 _ P s _
    ((h.pt c).of_extTo (I.Q_subset_SQ a) hdis) hp₀.uni (by subst hJ; exact δ.2) (hN ▸ hp₀.lat) d1 d2
    (fun w hw => d3 w fun e => ?_) (h.k_T _ P) (fun r j hr => hz ▸ d4 r j hr) ?_ ?_
  · rcases hw with hw | hw | ⟨hw, hne⟩
    · exact T_notMem_vGs hPr u ⟨w, hw⟩ (hT w e)
    · exact GlobalTheory.Proof.NarrowJetMoments.notMem_of_mem_QE hI.sel_ok hw (hPr.T_prime u) (hI.T_mem u) (hT w e)
    · rcases hover w e with e' | e'
      · exact hne e'
      · refine conj_piT_notMem hPr u P ?_
        have h1 : X.piT u ∈ w.asIdeal := decoFin_mem_of_mem_divs hw
        rw [e'] at h1
        exact h1
  · exact congrArg (fun q : PtAt B.R I.sel (I.tup a) (I.cst a) u i => q.1.1.deco) (mv_dia _ P s)
  · exact (congrArg (fun q : PtAt B.R I.sel (I.tup a) (I.cst a) u i => q.1.1.fr) (mv_dia ((I.stp u a i).rep c) P s) :)


set_option maxHeartbeats 4000000 in
theorem dilTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}), I.ReadsK l Z u a i hi chOf K → (∀ β, FunKilled (K β).lev (X.piT u)) → I.IdY l Z u a i hi eY → I.IdV l u a eV → DilationCompatibleChart (D := (I.rec7 l Z)) (I.fm l u a) eY eV chOf (lat := fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) K := by
  intro B X I hI hPins l Z u a i hi bad Ch chOf K eY eV hR hs hY hV
  obtain ⟨k, hR⟩ := hR
  have hJ := ((GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hPins l Z).2.2.2 i hi).1
  have hch : ∀ v s c, chOf ((I.fm l u a).dil i v s c) = chOf c := fun v s c =>
    (hR.key _ _).2 ⟨rfl, cosetIn_rep I l u a i v s c⟩
  have hy : ∀ β (c : {c // chOf c = β}), ((K β).y c).1 = ((K (chOf c.1)).y ⟨c.1, rfl⟩).1 := by
    rintro _ ⟨c, rfl⟩
    rfl
  have key : ∀ v (s : ((I.atT l u a).Fv v)ˣ) (z : ℤ), (z : (I.atT l u a).Fv v) = s → ∀ β (c : {c // chOf c = β}) δ,
      IsDia (K β).lev (eV v).1 (eV v).2 z δ → ∃ x : (K β).lev.U,
        ((K β).y c * δ).1 = bc (n := Fin ((I.rec7 l Z).R.N i)) (inclE (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
          (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))
          ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))) *
            ((K β).y ⟨(I.fm l u a).dil i v s c.1, (hch v s c.1).trans c.2⟩).1 * x.1 ∧
        (((K β).lev.chi x : ℂˣ) : ℂ) =
          B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1)) : B.LLˣ) : B.LL) := by
    rintro v s z hz _ ⟨c, rfl⟩ δ hδ
    have h1 := isPt_dia I hI l u a i hR v s c hJ (K (chOf c)).lev rfl (eV v).1 (eV v).2 (hV v) (hs _ _ _) z hz δ hδ
    obtain ⟨x, hx1, hx2⟩ := exists_level I l u a i hR v s c δ.1 h1 (chOf c) (hch v s c)
    refine ⟨x, ?_, hx2⟩
    rw [hy (chOf c) ⟨(I.fm l u a).dil i v s c, _⟩]
    exact hx1
  have hU : ∀ b (g : (I.stp u a i).G b), (I.stp u a i).gam b g ∈
      UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) := fun b g => by
    rw [hJ]
    show cT _ _ * 1 * _ = 1
    rw [mul_one]
    exact ((l.ch u a).step i).unit b g
  refine ⟨hch, fun v s z hz β c δ hδ => ?_, fun v s z hz β c δ hδ g hg => ?_⟩
  · obtain ⟨x, hx, -⟩ := key v s z hz β c δ hδ
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ?_
    have hγ := hU c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))
    have hxU := (((K β).lev.U_eq x.1).1 x.2).1
    have hγ' : bc (n := Fin ((I.rec7 l Z).R.N i)) (inclE (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
        (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))
        ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))) ∈
          UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := by
      have := mul_mem (mul_mem ((K β).y c * δ).2 (inv_mem hxU))
        (inv_mem ((K β).y ⟨(I.fm l u a).dil i v s c.1, (hch v s c.1).trans c.2⟩).2)
      rwa [hx, mul_inv_cancel_right, mul_inv_cancel_right] at this
    exact ⟨⟨_, hγ'⟩, ⟨_, hγ, rfl⟩, ⟨x.1, hxU⟩, x.2, Subtype.ext hx⟩
  · obtain ⟨x, hx, hc⟩ := key v s z hz β c δ hδ
    funext t
    have h1 := hg _ (hU c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1))) _ ((K β).y c * δ) x hx (eY t)
      (eY (frMul B.fields.emb B.embLL ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1)))⁻¹ t)) (fun τ => by
        rw [hY, hY]
        have e := congrArg (fun q => q.1 τ) ((frEquiv B.fields.emb B.embLL
          ((I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (dp I u a i v s c.1)))).apply_symm_apply t)
        refine e.symm.trans ?_
        have e2 : embAt B.embLL B.fields.emb τ = Formalism.L2.Forms.embT (I.rec7 l Z) τ := FieldsLaws.embLL_comp_emb B τ
        unfold Formalism.L2.Forms.atInf
        rw [← e2]
        rfl)
    rw [h1, hc]
    rfl

end GlobalTheory.Mem.Col2.DiaChart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondOperatorsOnChartsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondOperators_on_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}), I.ReadsK l Z u a i hi chOf K → (∀ β, FunKilled (K β).lev (X.piT u)) → I.IdY l Z u a i hi eY → I.IdV l u a eV → DilationCompatibleChart (D := (I.rec7 l Z)) (I.fm l u a) eY eV chOf (lat := fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) K := by
  first | exact @GlobalTheory.Mem.Col2.DiaChart.dilTied | exact GlobalTheory.Mem.Col2.DiaChart.dilTied | (intros; apply GlobalTheory.Mem.Col2.DiaChart.dilTied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongr
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem char_eq_of_tameRep_congr : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)), ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → 0 < normV P - 1 → ((normV P - 1 : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (normV P - 1) = 1) → ∀ (σ σ' : G E Ω) (u u' : 𝓞 E), NX.TameRep P 1 σ u → NX.TameRep P 1 σ' u' → u - u' ∈ P.asIdeal → χ σ = χ σ' := by
  intro E Ω _ _ _ _ _ P O _ _ _ _ _ hO χ hχ hm hmP hk σ σ' u u' hσ hσ' huu
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A P := exists_isPlaceOver Ω P
  obtain ⟨ρ, hs, ϖ, π, hϖ, hϖ2, hπ, hv⟩ := GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ u hσ
  obtain ⟨ρ', hs', ϖ', π', hϖ', hϖ2', hπ', hv'⟩ := GlobalTheory.TameTauConj.tameRep_conj A P hA 1 σ' u' hσ'
  have hconj : ∀ a b : G E Ω, χ (a⁻¹ * b * a) = χ b := by
    intro a b
    rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  rw [← hconj ρ σ, ← hconj ρ' σ']
  set s := ρ⁻¹ * σ * ρ
  set s' := ρ'⁻¹ * σ' * ρ'
  set m := normV P - 1
  rw [zpow_one] at hv hv'
  rw [← GlobalTheory.TameTau.tame_quot_indep A P hA m hm hmP ϖ ϖ' hϖ hϖ2 hϖ' hϖ2' π π' hπ hπ' s' hs'] at hv'
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Submodule.zero_mem _)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hπ
    exact hϖ0 (by exact_mod_cast hπ)
  have hroot : ∀ t : G E Ω, (t π / π) ^ m = 1 := by
    intro t
    rw [div_pow, ← map_pow, hπ, AlgEquiv.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  have hlt : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P.asIdeal := by
    intro x
    exact hA x
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    rw [← hlt]
    simpa using h
  have hu : A.valuation (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) < 1 := by
    have := (hlt (u - u')).2 huu
    simpa using this
  have heq : s π / π = s' π / π := by
    refine root_eq_of_close A m (hroot s) (hroot s') hmv ?_
    have e : s π / π - s' π / π = (s π / π - algebraMap E Ω (u : E))
        + (algebraMap E Ω (u : E) - algebraMap E Ω (u' : E)) - (s' π / π - algebraMap E Ω (u' : E)) := by ring
    rw [e]
    exact Valuation.map_sub_lt _ (Valuation.map_add_lt _ hv hu) hv'
  exact GlobalTheory.T.continuous_char_eq_of_inertia_condition A P hA hO χ hχ m hm hmP (hk A hA) ϖ hϖ hϖ2 π hπ s hs s' hs'
    ((div_left_inj' hπ0).1 heq)

end GlobalTheory.TameTau
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongrStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameChar_eq_of_tameRep_congr : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)), ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → 0 < normV P - 1 → ((normV P - 1 : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (normV P - 1) = 1) → ∀ (σ σ' : G E Ω) (u u' : 𝓞 E), NX.TameRep P 1 σ u → NX.TameRep P 1 σ' u' → u - u' ∈ P.asIdeal → χ σ = χ σ' := by
  first | exact @GlobalTheory.TameTau.char_eq_of_tameRep_congr | exact GlobalTheory.TameTau.char_eq_of_tameRep_congr | (intros; apply GlobalTheory.TameTau.char_eq_of_tameRep_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepBeforeClNonempty
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.Mem.Col2.TC.stepBefore_cl_nonempty {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (u : B.Word) :
    Nonempty (I.stp u I.mu0 (B.R.m - 1)).Cl := by
  classical
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  have hL := hOk.idx_ok I.mu0
  obtain ⟨b0x, -⟩ := hL.last_uniq
  let b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) (B.R.m - 1) := ⟨some (cast (by rw [show B.R.m - 1 = B.R.m - 2 + 1 by omega]) b0x), by simp; omega⟩
  let q0 : (I.stp u I.mu0 (B.R.m - 1)).D b0 := ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) (DecoF.base B.fields.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K))).deco.1.N
      (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ))}), by
    show _ ∈ (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) (B.R.m - 1)).ys _
    rw [ysAt_ys_of_eq _ _ _ hmj]
    exact ⟨0, zero_mem _, rfl⟩⟩
  exact ⟨(I.stp u I.mu0 (B.R.m - 1)).cl b0 q0⟩


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.Col2.TC.levJ_herm_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → 1 ≤ B.R.m - 1 → ∃ H0 : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (I.rec7 l Z).host.g (B.T u) B.R.f, F.levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) H0.Lb ∧ ∀ v, F.levJ.Uloc v = (H0.Uloc v).map (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF h1
  have hi : B.R.m - 1 ≤ (I.rec7 l Z).R.m := Nat.sub_le _ _
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) hi).1
  haveI : NeZero ((I.rec7 l Z).R.N (B.R.m - 1)) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s F.atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  obtain ⟨c0⟩ := GlobalTheory.Mem.Col2.TC.stepBefore_cl_nonempty I hI u
  obtain ⟨k, H⟩ := hF.mid (B.R.m - 1) h1 (succ_pred_m _)
  have hLb : ∀ x, x ∈ F.levJ.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N (B.R.m - 1)) (X.piT u) := by
    intro x
    rw [← F.levJ_Lb h1 (chOf0 (B.R.m - 1) c0)]
    exact H.lb _ x
  have hL : F.levJ.Lb = rll_dLat ((I.rec7 l Z).R.N (B.R.m - 1)) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 F.levJ.Lb ?_
    rw [hF.piU]; exact hLb
  have hE := GlobalTheory.Mem.Col2.Lv.exists_herm_level (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) (rankN (I.rec7 l Z) (B.R.m - 1) hi)
    (I.rec7 l Z).host.g _ _ rfl F.levJ ?_ ?_ ?_
  · obtain ⟨L, e1, e2, -⟩ := hE
    exact ⟨L, e1, e2⟩
  · intro v h0 h1 hb
    rcases hb with hb | hb
    · exact h0 hb
    · exact h1 hb
  · intro a v h x hx hp
    exact GlobalTheory.Mem.LevCong.mem_Uloc_of_cong _ F.levJ F.gl F.glevJ a v h x hx hp
  · intro v h x
    exact GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram F.levJ F.atT.piU (s F.atT.piU) rfl hpq hTp hL v h (GlobalTheory.T.levelPrime_dvd_of_adicValuation_lt_one (I.rec7 l Z) u F.atT v h) x

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsK1PointCongruent
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsK1PointCongruent
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.ColAd

theorem exists_K1_isPtOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → ∀ c : ℕ, ∃ z ∈ K1 hc n ST SG, (∀ P : Q, Sm Valued.v (dep P.1 c) (locM P.1 z - 1)) ∧ ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * z) p := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q hQ g hg c
  classical
  have hcc : ∀ P : HeightOneSpectrum (𝓞 E), conjPrime₂ (conjPrime₂ P) = P := fun P => by
    ext b
    rw [mem_conjP, mem_conjP, cO_cO]
  obtain ⟨p, hp⟩ := exists_near (ST := ST) (SG := SG) (Q := Q) hc c hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := congrArg Deco.N hp.deco
  obtain ⟨g', hg', c1, c2, c3⟩ := PtExist.exists_modify (fun P hP => (hQ P hP).2.2.2.2) hg (ptFr p)
    fun P _ => hN ▸ isFr_ptFr p P
  have hoff : ∀ P, P ∈ ST ∨ P ∈ SG → P ∉ Q ∧ conjPrime₂ P ∉ Q := fun P hP => by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hP with hP | hP
      · exact (hQ P h).1 hP
      · exact (hQ P h).2.1 hP
    · have := hQ _ h
      rw [hcc] at this
      rcases hP with hP | hP
      · exact this.2.2.1 hP
      · exact this.2.2.2.1 hP
  have hpt : IsPtOf hc g' p := by
    refine ⟨hg', hN ▸ c1, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P i j => ?_⟩
    · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
      rw [← hN] at hv
      have ho := hoff P.1 (Or.inl P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv), e]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [← hN] at hv
      have ho := hoff P.1 (Or.inr P.2)
      rw [c3 _ ho.1 ho.2, ← hp.deco]
      simp only [decoRaw]
      rw [if_pos (le_locP _ _ hv)]
      exact PtExist.hasRes_redA _ ((mem_globLat g v).1 hv i)
    · rw [c2 _ P.2, ptFr_of_mem p (hQ P.1 P.2).2.1 P.2]
      rfl
  have hd : decoRaw ST SG g = decoRaw ST SG g' := hp.deco.trans (near_of_isPtOf hpt c).deco.symm
  refine ⟨g⁻¹ * g', mem_principal_of_same_decoration hc n ST SG hg hg' hd, fun P => ?_, p, by rwa [mul_inv_cancel_left]⟩
  have e : locM P.1 g' = ratM P.1 (p.fr P) := Matrix.ext fun i j => hpt.fr P i j
  rw [locM_mul, e]
  exact hp.fr P

end GlobalTheory.Mem.ColAd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsK1PointCongruentStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_K1_point_congruent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) [NeZero n] (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ Q, P ∉ ST ∧ P ∉ SG ∧ conjPrime₂ P ∉ ST ∧ conjPrime₂ P ∉ SG ∧ conjPrime₂ P ∉ Q) → ∀ (g : GL (Fin n) (AfE F E)), g ∈ UAd hc n → ∀ c : ℕ, ∃ z ∈ K1 hc n ST SG, (∀ P : Q, Sm Valued.v (dep P.1 c) (locM P.1 z - 1)) ∧ ∃ p : DecoF E n ST SG Q, IsPtOf hc (g * z) p := by
  first | exact @GlobalTheory.Mem.ColAd.exists_K1_isPtOf | exact GlobalTheory.Mem.ColAd.exists_K1_isPtOf | (intros; apply GlobalTheory.Mem.ColAd.exists_K1_isPtOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPolarized
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SphNonSplit

theorem not_split_of_overPl (D : D7) {w w' : PlE D.host} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (hw : NG.OverPl w v) (hw' : NG.OverPl w' v) (hs : ¬ IsSplitPl D.host w) : ¬ IsSplitPl D.host w' := by
  intro hs'
  have hu : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w =
      HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w' :=
    HeightOneSpectrum.ext (hw.trans hw'.symm)
  have hr : Module.finrank (maximalRealSubfield D.host.E) D.host.E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj D.host.E) hr
      (IsCMField.complexConj_ne_one D.host.E) w' w).1 hu with h | h
  · exact hs (h ▸ hs')
  · have hc : (IsCMField.complexConj D.host.E).toRingEquiv = D.host.conj.toRingEquiv := by
      refine RingEquiv.ext fun x => ?_
      apply D.host.φ₀.injective
      show D.host.φ₀ (IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
      rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [hc] at h
    exact hs (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hs' ((GlobalTheory.Mem.Chr.conjPl_main.2.1 _ _ w' w).2 h))

theorem split_of_over_g (D : D7) (k : Fin 2) {w : PlE D.host} (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    IsSplitPl D.host w := by
  obtain ⟨u, h | h⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · rw [h]; exact GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u
  · exact GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u) h

theorem not_mem_bad (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v)
    (w0 : D.what₂.places.Pl) (j : Fin D.R.m) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hw : NG.OverPl w v) (hs : ¬ IsSplitPl D.host w) :
    v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w0) j) := by
  have hg : v ∉ gPl D := by
    rintro ⟨w', hw', k, hk⟩
    exact not_split_of_overPl D hw hw' hs (split_of_over_g D k hk)
  rintro (h | h)
  · exact hg h
  · rw [qPl_tup] at h
    obtain ⟨-, w', hw', hr⟩ := h
    apply not_split_of_overPl D hw hw' hs
    rw [tp.xi_tw] at hr
    by_contra hns
    apply hr
    have hpsi : (tp.psi w0).UnrAt w' := by
      obtain ⟨Q, hQ⟩ := tp.psi_gen w0
      exact (hQ.ram w').2 fun hq => hns (hQ.split w' hq)
    by_cases hl : D.what₂.places.resChar w0 = D.host.pde
    · have hd : cf.del'.UnrAt w' := cf.isDel'.unr w' fun hp => hns (hsp w' (Or.inr hp))
      intro x hx
      simp only [Host.CharFrame.delAt, hl, ↓reduceIte]
      change cf.del'.loc w' x * (tp.psi w0).loc w' x = 1
      rw [hd x hx, hpsi x hx, one_mul]
    · have hd : cf.del.UnrAt w' := cf.isDel.unr w' fun hp => hns (hsp w' (Or.inl hp))
      intro x hx
      simp only [Host.CharFrame.delAt, hl, ↓reduceIte]
      change cf.del.loc w' x * (tp.psi w0).loc w' x = 1
      rw [hd x hx, hpsi x hx, one_mul]

end GlobalTheory.SphNonSplit

namespace GlobalTheory.SphNonSplit

end GlobalTheory.SphNonSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidue
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.TameRes

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_int_le_one (A : ValuationSubring Ω) (c : 𝓞 E) : A.valuation (algebraMap E Ω (c : E)) ≤ 1 := by
  refine (A.valuation_le_one_iff _).2 ?_
  have hi : IsIntegral ℤ (algebraMap E Ω (c : E)) := c.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom
  have h1 : IsIntegral A (algebraMap E Ω (c : E)) := hi.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).mp h1
  rw [← hy]
  exact y.2

theorem val_le_of_unif {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hA : IsPlaceOver (F := E) A P)
    {a b : 𝓞 E} (ha : a ∈ P.asIdeal) (hb : b ∈ P.asIdeal) (hb' : b ∉ P.asIdeal ^ 2) :
    A.valuation (algebraMap E Ω a) ≤ A.valuation (algebraMap E Ω b) := by
  obtain ⟨I, hI⟩ : P.asIdeal ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hb)
  have h1 : ¬ I ≤ P.asIdeal := fun h => hb' (by
    rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]; exact Ideal.mul_mono_right h)
  obtain ⟨s, hs, hs'⟩ := Set.not_subset.1 h1
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 (hI ▸ Ideal.mul_mem_mul ha hs)
  have h2 : A.valuation (algebraMap E Ω s) = 1 :=
    le_antisymm (val_int_le_one A s) (not_lt.1 fun h => hs' ((hA s).1 h))
  have h3 := congrArg (fun c : 𝓞 E => A.valuation (algebraMap E Ω c)) ht
  have hint := val_int_le_one (E := E) A t
  simp only [map_mul, RingOfIntegers.coe_eq_algebraMap] at h3 h2 hint ⊢
  rw [h2, mul_one] at h3
  rw [h3]
  exact mul_le_of_le_one_right' hint

theorem redThrough_eq_of_val_sub {A : ValuationSubring Ω} {l : ℕ} [Fact l.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar l) {z w : Ω} (hz : z ∈ A) (hw : w ∈ A)
    (h : A.valuation (z - w) < 1) : redThrough A κ z = redThrough A κ w := by
  unfold redThrough
  rw [dite_eq_left hz, dite_eq_left hw]
  congr 1
  apply Ideal.Quotient.eq.2
  exact (A.valuation_lt_one_iff (⟨z, hz⟩ - ⟨w, hw⟩)).2 h

end GlobalTheory.TameRes

namespace GlobalTheory.TameRes

theorem exists_nat_sub_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime]
    (hN : normV P = g) (hgP : ((g : ℕ) : 𝓞 E) ∈ P.asIdeal) (u : 𝓞 E) :
    ∃ a : ℕ, a < g ∧ u - (a : 𝓞 E) ∈ P.asIdeal := by
  have hgp : g.Prime := Fact.out
  haveI := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field _
  haveI : CharP (𝓞 E ⧸ P.asIdeal) g := by
    rw [CharP.charP_iff_prime_eq_zero hgp, ← map_natCast (Ideal.Quotient.mk P.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hgP
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = g := hN
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hgp.ne_zero)
  let f : ZMod g →+* 𝓞 E ⧸ P.asIdeal := ZMod.castHom (dvd_refl g) _
  have hsurj : Function.Surjective f :=
    (Function.Injective.bijective_of_nat_card_le f.injective (by rw [hcard, Nat.card_zmod])).2
  obtain ⟨x, hx⟩ := hsurj (Ideal.Quotient.mk P.asIdeal u)
  refine ⟨x.val, ZMod.val_lt x, ?_⟩
  apply Ideal.Quotient.eq.1
  rw [← hx, map_natCast]
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact map_natCast f x.val

end GlobalTheory.TameRes


open GlobalTheory.TameRes in
theorem GlobalTheory.tameRep_residue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime], IsPlaceOver (F := E) A P → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g), σ ∈ Ine (F := E) A → IsGenSys ζ → TameCoupled A κ σ ζ → (∀ A' : ValuationSubring Ω, IsPlaceOver (F := E) A' P → σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A) → ∀ u : 𝓞 E, NX.TameRep P 1 σ u → ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧ algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  intro E Ω _ _ _ _ _ A P g _ hAP hN hgP hgP2 κ σ ζ hσ hζ hT huniq u hu
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hgp : g.Prime := Fact.out
  have hg2 : 2 ≤ g := hgp.two_le
  have hgΩ : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  have hg4 : 4 ≤ g ^ 2 := by nlinarith

  have hσ1 : σ ≠ 1 := by
    rintro rfl
    have hpos : 0 < g ^ 2 - 1 := by omega
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hpos
    have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hpos.ne'] at hy; exact hgΩ hy.symm
    have h2 := hT 2 (by norm_num) y hy
    rw [AlgEquiv.one_apply, div_self hy0, redThrough_one] at h2
    have ho := (hζ 2 (by norm_num)).1
    rw [← h2, orderOf_one] at ho
    omega
  obtain ⟨A', hA'P, hσA', ϖ, π, hϖ, hϖ2, hπ, hv⟩ := hu
  have hAA : A' = A := huniq A' hA'P hσA' hσ1
  rw [hAA] at hv
  rw [hN] at hπ
  simp only [zpow_one] at hv

  have hg1 : 0 < g - 1 := by omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((g : ℕ) : Ω) hg1
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hg1.ne'] at hy; exact hgΩ hy.symm
  have hTy : redThrough A κ (σ y / y) = ζ 1 := hT 1 one_pos y (by rw [pow_one]; exact hy)
  have hϖ0 : algebraMap E Ω (ϖ : E) ≠ 0 := by
    rw [ne_eq, map_eq_zero, RingOfIntegers.coe_eq_zero_iff]
    rintro rfl; exact hϖ2 (zero_mem _)
  have hπ0 : π ≠ 0 := by rintro rfl; rw [zero_pow hg1.ne'] at hπ; exact hϖ0 hπ.symm
  have hϖg : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation ((g : ℕ) : Ω) := by
    have e : ((g : ℕ) : Ω) = algebraMap E Ω (((g : ℕ) : 𝓞 E) : E) := by simp
    rw [e]
    exact le_antisymm (val_le_of_unif hAP hϖ hgP hgP2) (val_le_of_unif hAP hgP hϖ hϖ2)
  have hπy : A.valuation π = A.valuation y := by
    have h1 : A.valuation π ^ (g - 1) = A.valuation y ^ (g - 1) := by
      rw [← map_pow, ← map_pow, hπ, hy, hϖg]
    exact (pow_left_inj hg1.ne').mp h1
  have hvy0 : A.valuation y ≠ 0 := by simpa using hy0
  have hw1 : A.valuation (π / y) = 1 := by rw [map_div₀, hπy, div_self hvy0]
  have hwσ : A.valuation (σ (π / y) - π / y) < 1 := hσ.2 _ hw1.le
  have hσy0 : σ y ≠ 0 := fun h => hy0 (σ.injective (by rw [h, map_zero]))
  have key : σ π / π - σ y / y = (σ y / y) * ((σ (π / y) - π / y) / (π / y)) := by
    rw [map_div₀]
    field_simp
  have hq : A.valuation (σ y / y) ≤ 1 := (A.valuation_le_one_iff _).2 (tameQuot_mem A σ hg1 hgΩ hy)
  have h1 : A.valuation (σ π / π - σ y / y) < 1 := by
    rw [key, map_mul, map_div₀ A.valuation (σ (π / y) - π / y), hw1, div_one]
    calc A.valuation (σ y / y) * A.valuation (σ (π / y) - π / y)
        ≤ 1 * A.valuation (σ (π / y) - π / y) := by gcongr
      _ < 1 := by rw [one_mul]; exact hwσ

  obtain ⟨a, -, hua⟩ := exists_nat_sub_mem P g hN hgP u
  have hua' : A.valuation (algebraMap E Ω (u : E) - (a : Ω)) < 1 := by
    have := (hAP (u - (a : 𝓞 E))).2 hua
    simpa using this
  have h3 : A.valuation (σ y / y - (a : Ω)) < 1 := by
    have e : σ y / y - (a : Ω) = -(σ π / π - σ y / y) + (σ π / π - algebraMap E Ω (u : E)) +
        (algebraMap E Ω (u : E) - (a : Ω)) := by ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ ?_ hv) hua'
    rw [Valuation.map_neg]; exact h1
  have haA : (a : Ω) ∈ A := by exact_mod_cast (natCast_mem A a)
  have hred : redThrough A κ (σ y / y) = (a : Formalism.CyclotomicNorms.Fbar g) := by
    rw [redThrough_eq_of_val_sub κ (tameQuot_mem A σ hg1 hgΩ hy) haA h3]
    unfold redThrough
    rw [dite_eq_left haA]
    have : (⟨(a : Ω), haA⟩ : A) = (a : A) := Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast]
  have hz : ζ 1 = (a : Formalism.CyclotomicNorms.Fbar g) := by rw [← hTy, hred]
  refine ⟨a, ?_, hua, by rw [map_natCast, hz]⟩
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hgp]
  intro hd
  have h0 : (a : Formalism.CyclotomicNorms.Fbar g) = 0 := (CharP.cast_eq_zero_iff (Formalism.CyclotomicNorms.Fbar g) g a).2 hd
  have ho := (hζ 1 one_pos).1
  rw [hz, h0, pow_one] at ho
  have hz0 : orderOf (0 : Formalism.CyclotomicNorms.Fbar g) = 0 := by
    rw [orderOf_eq_zero_iff']
    intro n hn
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]
    exact zero_ne_one
  omega
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaRepresentativeResidueStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameInertia_representative_residue : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) [Fact g.Prime], IsPlaceOver (F := E) A P → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ((g : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (σ : G E Ω) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g), σ ∈ Ine (F := E) A → IsGenSys ζ → TameCoupled A κ σ ζ → (∀ A' : ValuationSubring Ω, IsPlaceOver (F := E) A' P → σ ∈ Ine (F := E) A' → σ ≠ 1 → A' = A) → ∀ u : 𝓞 E, NX.TameRep P 1 σ u → ∃ a : ℕ, a.Coprime g ∧ u - (a : 𝓞 E) ∈ P.asIdeal ∧ algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) (a : ZMod g) = ζ 1 := by
  first | exact @GlobalTheory.tameRep_residue | exact GlobalTheory.tameRep_residue | (intros; apply GlobalTheory.tameRep_residue <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainLevelFamilyExtension
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3 GlobalTheory.Mem.ColTie

noncomputable section

namespace GlobalTheory.Mem.ColTie

theorem map_pairV_one {E K ι : Type} [Field E] [Field K] [StarRing K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K)
    (lam : ι → DomWeight n) (σ : K →+* ℂ) (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) (x y : VV K lam) :
    σ (pairV emb lam 1 x y) =
      pairB lam (MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map σ x.1)) (MvPolynomial.map σ y.1) := by
  have e : gramK emb (1 : Matrix (Fin n) (Fin n) E) = fun τ => (((1 : ι → GL (Fin n) K) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    funext τ
    rw [gramK, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  show σ (pairK lam (gramK emb 1) x y) = _
  rw [pairK_apply, e, pairP_eq_pairB, polyAction_one₂, GlobalTheory.PeriodOnStep.map_pairB, MvPolynomial.map_map,
    MvPolynomial.map_map]
  congr 2
  exact congrArg (fun f => MvPolynomial.map f (x : Pol K ι n)) (RingHom.ext fun a => hσ a)

end GlobalTheory.Mem.ColTie
end
end
