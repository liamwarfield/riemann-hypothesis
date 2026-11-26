module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetFramesInvariantRationalUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetFramesInvariantRationalUnitary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2


open Classical GlobalTheory.TopStep in
theorem cosetIn_smul_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → ∀ (q q' : PtAt R sel mu cst u j) (γ : UF X.E (R.N j)), q'.1.1 = ((γ, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • q.1.1 → q'.1.2 = (fun z => γ.1 z) '' q.1.2 → cosetIn q' = cosetIn q := by
  intro X Pr R sel S mu cst u j hX hPr q q' γ h1 h2
  funext P
  have key : ∀ y ∈ q.1.2, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ •
      ((frsF sel mu q'.1.1 P).symm (γ.1 y) - (frsF sel mu q.1.1 P).symm y) ∈ stdAt X.E (R.N j) P.1 := by
    intro y hy
    by_cases hP : P.1 ∈ Pr.vGs
    · rw [if_pos hP, pow_zero, inv_one, one_smul]
      by_cases hj : j + 1 = R.m
      swap
      · have h0 : q.1.2 = ∅ := by
          have := q.2
          rw [ysAt_ys_of_ne sel mu cst hj] at this
          exact this
        rw [h0] at hy
        exact absurd hy (Set.notMem_empty y)
      obtain ⟨y0, hy0, hY⟩ := PtAt.mem_ybSet q hj
      have hy' : y - y0 ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N
          (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
        rw [hY] at hy
        exact hy
      have hA : (qOf P.1 : X.E) • y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal q.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy0 P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hB : y - y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal q.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy' P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hx : (qOf P.1 : X.E) • y ∈ q.1.1.deco.1.at P.1 := by
        have e : (qOf P.1 : X.E) • y = (qOf P.1 : X.E) • y0 + (qOf P.1 : X.E) • (y - y0) := by
          rw [← smul_add, add_sub_cancel]
        rw [e]
        exact add_mem hA (smul_mem_locP (intAt_nat _) hB)
      let w : Pr.vGs := ⟨P.1, hP⟩
      have hd : q'.1.1.deco.1 = q.1.1.deco.1.act γ.1 1 := by
        rw [h1]
        rfl
      have hf : IsLiftFr q.1.1.deco.1 w (q.1.1.deco.1.liftFr w) := liftFr_spec q.1.1.deco.2 w
      have hf' : IsLiftFr (q.1.1.deco.1.act γ.1 1) w (q'.1.1.deco.1.liftFr w) := by
        rw [← hd]
        exact liftFr_spec q'.1.1.deco.2 w
      have e1 : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      have e2 : frsF sel mu q'.1.1 P = q'.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      rw [e1, e2]
      let κ := passFr γ.1 1 hf hf'
      have hκ : redGL (R.N j) P.1 κ = 1 := redGL_passFr γ.1 1 hf hf'
      set f := q.1.1.deco.1.liftFr w
      set f' := q'.1.1.deco.1.liftFr w
      have e3 : f'.symm (γ.1 y) = κ.1 (f.symm y) := by
        show _ = f'.symm (γ.1 (f (f.symm y)))
        rw [LinearEquiv.apply_symm_apply]
      rw [e3]
      have hv0 : f.symm ((qOf P.1 : X.E) • y) ∈ stdAt X.E (R.N j) P.1 := by
        rw [← hf.1, LinearEquiv.apply_symm_apply]
        exact hx
      rw [map_smul] at hv0
      have hred := redV_redGL κ hv0
      rw [hκ, Units.val_one, Matrix.one_mulVec] at hred
      have hq := (degOneUnram_of_mem_vGs hX hPr hP).2
      have hq0 : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
      refine mem_stdAt.2 fun i => ?_
      have hi1 := mem_stdAt.1 (glint_mem κ hv0) i
      have hi2 := mem_stdAt.1 hv0 i
      have hr : redP P.1 ((κ.1 ((qOf P.1 : X.E) • f.symm y) - (qOf P.1 : X.E) • f.symm y) i) = 0 := by
        rw [Pi.sub_apply, reduction_sub hi1 hi2, sub_eq_zero]
        exact congrFun hred i
      have := intAt_div_of_redP hq (intAt_sub hi1 hi2) hr
      convert this using 1
      rw [map_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    · rw [if_neg hP]
      have e : (frsF sel mu q'.1.1 P).symm (γ.1 y) = (frsF sel mu q.1.1 P).symm y := by
        rw [LinearEquiv.symm_apply_eq]
        unfold frsF
        rw [dite_eq_right hP, dite_eq_right hP, h1]
        show γ.1 y = γ.1 (q.1.1.fr _ ((((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 ((q.1.1.fr _).symm y)))
        simp
      rw [e, sub_self, smul_zero]
      exact zero_mem _
  ext z
  simp only [cosetIn, Set.mem_setOf_eq]
  rw [h2]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨y, hy, ?_⟩
    have := add_mem hz (key y hy)
    rwa [← smul_add, sub_add_sub_cancel] at this
  · rintro ⟨y, hy, hz⟩
    refine ⟨γ.1 y, ⟨y, hy, rfl⟩, ?_⟩
    have := sub_mem hz (key y hy)
    rwa [← smul_sub, sub_sub_sub_cancel_right] at this

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetFramesInvariantRationalUnitaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_frames_invariant_rational_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → ∀ (q q' : PtAt R sel mu cst u j) (γ : UF X.E (R.N j)), q'.1.1 = ((γ, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • q.1.1 → q'.1.2 = (fun z => γ.1 z) '' q.1.2 → cosetIn q' = cosetIn q := by
  exact @GlobalTheory.Mem.Col2.cosetIn_smul_unitary
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemField
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemField
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.HeckeValField

variable {E : Type} [Field E] [NumberField E]

def unitsIn (M : IntermediateField ℚ ℂ) : Subgroup ℂˣ where
  carrier := {z | (z : ℂ) ∈ M}
  one_mem' := by simpa using M.one_mem
  mul_mem' := fun {a b} ha hb => by simpa using M.mul_mem ha hb
  inv_mem' := fun {a} ha => by simpa using M.inv_mem ha

theorem mem_unitsIn {M : IntermediateField ℚ ℂ} {z : ℂˣ} : z ∈ unitsIn M ↔ (z : ℂ) ∈ M := Iff.rfl

theorem val_mem (χ : HChar E) {M : IntermediateField ℚ ℂ} (hM : valueField χ 0 ≤ M)
    {v : HeightOneSpectrum (𝓞 E)} (hv : χ.UnrAt v) : χ.val v ∈ unitsIn M := by
  have h := hM (IntermediateField.subset_adjoin ℚ (valueSet χ 0) ⟨v, hv, rfl⟩)
  exact mem_unitsIn.2 (by simpa [HChar.valTw] using h)

theorem loc_mem_of_unrAt (χ : HChar E) {G : Subgroup ℂˣ} {v : HeightOneSpectrum (𝓞 E)} (hv : χ.UnrAt v)
    (hval : χ.val v ∈ G) (y : (v.adicCompletion E)ˣ) : χ.loc v y ∈ G := by
  set π := atFin v (unif v)
  have hπ : Valued.v (π : v.adicCompletion E) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hy0 : Valued.v (y : v.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr y.ne_zero
  set k := WithZero.log (Valued.v (y : v.adicCompletion E))
  have hy : Valued.v (y : v.adicCompletion E) = WithZero.exp k := (WithZero.exp_log hy0).symm
  have hu : IsUnitAt v (y * π ^ k) := by
    unfold IsUnitAt
    rw [Units.val_mul, map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, hy, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp
  have h1 := hv _ hu
  rw [map_mul, map_zpow] at h1
  rw [eq_inv_of_mul_eq_one_left h1]
  exact G.inv_mem (G.zpow_mem hval k)

theorem loc_mem (χ : HChar E) {M : IntermediateField ℚ ℂ} (hM : valueField χ 0 ≤ M)
    (hinf : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ) :
    χ.loc v y ∈ unitsIn M := by
  classical
  set G := unitsIn M
  by_cases hv : χ.UnrAt v
  · exact loc_mem_of_unrAt χ hv (val_mem χ hM hv) y
  set R := (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have hR : ∀ w, w ∉ R → χ.UnrAt w := fun w hw => by
    by_contra h
    exact hw ((GlobalTheory.Mem.UnrAe.finite_ramified χ).mem_toFinset.2 h)
  choose nf hnf using GlobalTheory.HeckeSplit.exists_level χ.1 χ.2.1
  set S := insert v R
  set N := S.sup nf
  obtain ⟨a, ha0, hav, haw⟩ := GlobalTheory.HkFin.exists_weak_approx_unit E R v y N
  set k : Eˣ := Units.mk0 a ha0
  have h1 : χ.loc v y = χ.locK v k := by
    have hle : nf v ≤ N := Finset.le_sup (Finset.mem_insert_self v R)
    have e : χ.loc v (atFin v k * y⁻¹) = 1 := by
      apply hnf v
      refine le_trans ?_ (WithZero.exp_le_exp.mpr (by omega : -(N : ℤ) ≤ -(nf v : ℤ)))
      exact hav
    rw [map_mul, map_inv, mul_inv_eq_one] at e
    exact e.symm
  have h2 : ∀ w ∈ S, w ≠ v → χ.locK w k = 1 := by
    intro w hw hwv
    have hwR : w ∈ R := (Finset.mem_insert.1 hw).resolve_left hwv
    have hle : nf w ≤ N := Finset.le_sup hw
    apply hnf w
    have e : ((atFin w k : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1 =
        algebraMap E (w.adicCompletion E) (a - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e, PI.FinOrdValD.WA.val_alg]
    exact (haw w hwR hwv).trans (WithZero.exp_le_exp.mpr (by omega))
  have hpr := χ.productRule S (fun w hw => hR w fun h => hw (Finset.mem_insert_of_mem h)) k
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_insert_self v R) (fun w hw hwv => h2 w hw hwv)] at hpr
  have hF : (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : w ∉ S), χ.val w ^ ordF w k) ∈ G := by
    refine finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun w => ?_
    refine finprod_induction (· ∈ G) G.one_mem (fun _ _ => G.mul_mem) fun hw => ?_
    exact G.zpow_mem (val_mem χ hM (hR w fun h => hw (Finset.mem_insert_of_mem h))) _
  have h3 : χ.locK v k * (χ.inf k * ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : w ∉ S), χ.val w ^ ordF w k) = 1 := by
    rw [← hpr]; ac_rfl
  rw [h1, eq_inv_of_mul_eq_one_left h3]
  exact G.inv_mem (G.mul_mem (hinf k) hF)

theorem mem_of_inf_eq_one : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (M : IntermediateField ℚ ℂ),
    valueField χ 0 ≤ M → (∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x, (∀ w : InfinitePlace E,
      (x.val : AdeleRing (𝓞 E) E).1 w = 1) → ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  intro E _ _ χ M hM hinf x hx
  classical
  have hev : ∀ᶠ v in Filter.cofinite, Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) :
      v.adicCompletion E) = 1 := by
    have h1 : ∀ᶠ v in Filter.cofinite, (x.val.2 : FiniteAdeleRing (𝓞 E) E).1 v ∈ v.adicCompletionIntegers E :=
      x.val.2.2
    have h2 : ∀ᶠ v in Filter.cofinite, (x⁻¹.val.2 : FiniteAdeleRing (𝓞 E) E).1 v ∈ v.adicCompletionIntegers E :=
      x⁻¹.val.2.2
    filter_upwards [h1, h2] with v hv1 hv2
    have e1 : Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv1
    have e2 : Valued.v ((GlobalTheory.HeckeSplit.finPart E v x⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hv2
    rw [map_inv, Units.val_inv_eq_inv_val, map_inv₀] at e2
    have h0 : 0 < Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) :=
      zero_lt_iff.2 ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))
    exact le_antisymm e1 ((inv_le_one₀ h0).1 e2)
  have hfin := Filter.eventually_cofinite.1 hev
  set S := hfin.toFinset ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have hS : ∀ v ∉ S, χ.1 (HeckeValGen.localIdele E v (GlobalTheory.HeckeSplit.finPart E v x)) = 1 := by
    intro v hv
    have hu : ¬ ¬ Valued.v ((GlobalTheory.HeckeSplit.finPart E v x : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1 :=
      fun h => hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 h))
    have hr : χ.UnrAt v := by
      by_contra h
      exact hv (Finset.mem_union_right _ ((GlobalTheory.Mem.UnrAe.finite_ramified χ).mem_toFinset.2 h))
    exact hr _ (not_not.1 hu)
  rw [GlobalTheory.HeckeSplit.char_eq_prod_local χ.1 χ.2.1 x S hS]
  have hinfx : GlobalTheory.HeckeSplit.infPart E x = 1 := Units.ext (funext fun w => hx w)
  rw [hinfx, map_one, map_one, one_mul]
  exact mem_unitsIn.1 ((unitsIn M).prod_mem fun v _ => loc_mem χ hM hinf v _)

end GlobalTheory.HeckeValField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemFieldStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_finiteIdele_value_mem_field : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (M : IntermediateField ℚ ℂ), valueField χ 0 ≤ M → (∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M) → ∀ x, (∀ w : InfinitePlace E, (x.val : AdeleRing (𝓞 E) E).1 w = 1) → ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  first | exact @GlobalTheory.HeckeValField.mem_of_inf_eq_one | exact GlobalTheory.HeckeValField.mem_of_inf_eq_one | (intros; apply GlobalTheory.HeckeValField.mem_of_inf_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoStabTrivial
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TwAtStd

theorem ptY_mv_deco {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n}
    (p : PtY ST SG Q y) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))
    (h1 : ∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) (h2 : p.1.2 ∈ y.ys d.1.N) :
    (p.mv d).1.1.deco = d := by
  have e : p.mv d = (⟨(⟨(d, p.1.1.1.2), h1⟩, p.1.2), h2⟩ : PtY ST SG Q y) := dif_pos ⟨h1, h2⟩
  rw [e]
  rfl

theorem diaPt_deco (B : Base) (X : PreX B.toPre) (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u a i).Cl) :
    (((I.atIn u a).A i).diaPt P x c).1.1.deco = DecoSet.dia1 P x ((I.stp u a i).rep c).1.1.deco :=
  ptY_mv_deco ((I.stp u a i).rep c) _ (fun Q y => ((I.stp u a i).rep c).1.1.2 Q y) ((I.stp u a i).rep c).2

theorem dil_eCls0 (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.atIn u a).dil 0 P x (I.eCls0 l u a c) = I.eCls0 l u a ((I.atIn u I.mu0).dil 0 P x c) := by
  show (I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)) =
    I.cl0 u a (l.idx0 a).some ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  refine (ClsZero.cl_eq_iff hI u a _ _ _ _).2 ?_
  rw [diaPt_deco, ClsZero.stepZero_corresponding_representatives_same_deco hI]
  have e := (ClsZero.cl_eq_iff hI u I.mu0 _ _ _ _).1
    (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c)))
  show _ = ClsZero.canon _ ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco
  rw [e, diaPt_deco]

theorem deco_stab_trivial (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (b : (I.stp u a 0).β) (p : (I.stp u a 0).D b) (γ : UF B.fields.E (B.R.N 0)) (k : GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))
    (hk : k ∈ (colLev I.Ch 0).grp) (h : ((γ, k) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • p.1.1.deco = p.1.1.deco) :
    γ = 1 ∧ k = 1 := by
  have hfree : (I.stp u a 0).Free := (l.lev u a).free0
  let q : DecoF B.fields.E (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup a)) :=
    ((γ, k, 1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs) × GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a))) • p.1.1
  have hq : q.deco = p.1.1.deco := h
  have hc : ∀ P : QE I.sel (I.tup a), (p.1.1.fr P)⁻¹ * q.fr P ∈ GLint B.fields.E (B.R.N 0) P.1 := by
    intro P x
    have h1 := q.2 P x
    have h2 := p.1.1.2 P ((p.1.1.fr P)⁻¹ (q.fr P x))
    have h3 : p.1.1.1.2 P ((p.1.1.fr P)⁻¹ (q.fr P x)) = q.fr P x := LinearEquiv.apply_symm_apply _ _
    rw [h3] at h2
    have h4 : q.1.1 = p.1.1.1.1 := hq
    rw [h4] at h1
    exact h2.symm.trans h1
  have hkG : k ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b).grp := by rw [ClsZero.levelTypePrimes_stepZero_eq_colLev hI]; exact hk
  let qq : GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a)) := fun P => ⟨(p.1.1.fr P)⁻¹ * q.fr P, hc P⟩
  have htop : ∀ Θ : LevQFam B.fields.E B.fields.K (B.R.N 0) (QE I.sel (I.tup a)), Θ = LevQFam.top _ _ _ _ → qq ∈ Θ.grp := by
    rintro _ rfl
    intro P _
    trivial
  have hqQ := htop _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a b)
  have key : ∀ (y : Ys B.fields (B.R.N 0)), y = Ys.triv _ _ → ∀ (S : Set (Sp B.fields.E (B.R.N 0))) N, S ∈ y.ys N → S = ∅ := by
    rintro _ rfl S N hS
    exact hS
  have hp0 : p.1.2 = ∅ := key _ (ClsZero.ys0 a) _ _ p.2
  let g : (I.stp u a 0).G b := (γ, ⟨k, hkG⟩, ⟨qq, hqQ⟩)
  have hg : (I.stp u a 0).act b g p = p := by
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h ?_)) ?_)
    · funext P
      show γ.1 * p.1.1.fr P * ((p.1.1.fr P)⁻¹ * (γ.1 * p.1.1.fr P * ((1 : GLQ B.fields.E (B.R.N 0) (QE I.sel (I.tup a))) P)⁻¹.1))⁻¹ = p.1.1.fr P
      simp only [Pi.one_apply, inv_one, OneMemClass.coe_one, mul_one]
      group
    · show (fun v => γ.1 v) '' p.1.2 = p.1.2
      rw [hp0, Set.image_empty]
  have e := hfree b g p hg
  exact ⟨congrArg Prod.fst e, congrArg (fun g : (I.stp u a 0).G b => (g.2.1 : GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))) e⟩

theorem chrG_eq {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (L Λ Λ' : LevFam E K n SG) (h : Λ = L) (h' : Λ' = L) (k : Λ.grp) (k' : Λ'.grp) (e : k.1 = k'.1) :
    Λ.chr k = Λ'.chr k' := by
  subst h h'
  rw [Subtype.ext e]

theorem chrQ_top {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 E))}
    (Θ : LevQFam E K n Q) (h : Θ = LevQFam.top E K n Q) (q : Θ.grp) : Θ.chr q = 1 := by
  subst h
  unfold LevQFam.chr piChar
  erw [Finset.prod_eq_one (fun i _ => MonoidHom.one_comp _)]
  rfl

theorem dilT_eCls0 (B : Base) (X : PreX B.toPre) (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (P : (B.primes X).vT u) (x : (Res P.1)ˣ) (c : (I.stp u I.mu0 0).Cl) :
    (I.atIn u a).dilT B.fields.emb B.embLL 0 P x (I.eCls0 l u a c) = (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 P x c := by
  show (I.stp u a 0).tr B.fields.emb B.embLL (I.cl0 u a (l.idx0 a).some c).1 ((I.stp u a 0).mv (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c))) = (I.stp u I.mu0 0).tr B.fields.emb B.embLL c.1 ((I.stp u I.mu0 0).mv c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  set ga := (I.stp u a 0).mv (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)) with hga
  set gm := (I.stp u I.mu0 0).mv c.1 (((I.atIn u I.mu0).A 0).diaPt P x c) with hgm
  have hA : ((ga.1, ga.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco :=
    congrArg (fun p : (I.stp u a 0).D (I.cl0 u a (l.idx0 a).some c).1 => p.1.1.deco) ((I.stp u a 0).mv_smul (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))
  have hM : ((gm.1, gm.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) •
      ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco :=
    congrArg (fun p : (I.stp u I.mu0 0).D c.1 => p.1.1.deco) ((I.stp u I.mu0 0).mv_smul c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))
  have hRA : ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = ClsZero.canon (colLev I.Ch 0) (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco :=
    (ClsZero.stepZero_representative_deco_eq_canonical hI u a _).trans ((ClsZero.cl_eq_iff hI u a _ _ _ _).1 (ClsZero.cl_rep (I.stp u a 0) ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))))
  have hRM : ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = ClsZero.canon (colLev I.Ch 0) (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco :=
    (ClsZero.stepZero_representative_deco_eq_canonical hI u I.mu0 _).trans ((ClsZero.cl_eq_iff hI u I.mu0 _ _ _ _).1 (ClsZero.cl_rep (I.stp u I.mu0 0) ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))))
  have hT : (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)).1.1.deco = (((I.atIn u I.mu0).A 0).diaPt P x c).1.1.deco := by
    rw [diaPt_deco, diaPt_deco, ClsZero.stepZero_corresponding_representatives_same_deco hI]
  have hR : ((I.stp u I.mu0 0).rep ((I.stp u I.mu0 0).cl c.1 (((I.atIn u I.mu0).A 0).diaPt P x c))).1.1.deco = ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco := by rw [hRA, hRM, hT]
  rw [hR, ← hT] at hM
  have hfix : (((gm.1, gm.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))⁻¹ *
      ((ga.1, ga.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))) •
      ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco = ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))).1.1.deco := by
    rw [mul_smul, hA, inv_smul_eq_iff, hM]
  have memG : ∀ Λ : LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs, Λ = colLev I.Ch 0 → ∀ k : Λ.grp, k.1 ∈ (colLev I.Ch 0).grp := by
    rintro _ rfl k
    exact k.2
  have hkA := memG _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI a _) ga.2.1
  have hkM := memG _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 _) gm.2.1
  obtain ⟨e1, e2⟩ := deco_stab_trivial B X I hI l u a (I.cl0 u a (l.idx0 a).some c).1 ((I.stp u a 0).rep ((I.stp u a 0).cl (I.cl0 u a (l.idx0 a).some c).1 (((I.atIn u a).A 0).diaPt P x (I.cl0 u a (l.idx0 a).some c)))) (gm.1⁻¹ * ga.1) (gm.2.1.1⁻¹ * ga.2.1.1)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkM) hkA) hfix
  have eγ : ga.1 = gm.1 := (inv_mul_eq_one.1 e1).symm
  have ek : ga.2.1.1 = gm.2.1.1 := (inv_mul_eq_one.1 e2).symm
  show trFr B.fields.emb B.embLL ((I.stp u a 0).gam (I.cl0 u a (l.idx0 a).some c).1 ga) ((I.stp u a 0).chr (I.cl0 u a (l.idx0 a).some c).1 ga) = trFr B.fields.emb B.embLL ((I.stp u I.mu0 0).gam c.1 gm) ((I.stp u I.mu0 0).chr c.1 gm)
  congr 1
  · show ufGL _ _ ga.1 = ufGL _ _ gm.1
    rw [eγ]
  · show (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 (I.cl0 u a (l.idx0 a).some c).1).chr ga.2.1 * (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 (I.cl0 u a (l.idx0 a).some c).1).chr ga.2.2 =
      (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr gm.2.1 * (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) 0 c.1).chr gm.2.2
    rw [chrQ_top _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI a _), chrQ_top _ (ClsZero.chartIndexLevelTwistPrimes_stepZero_eq_top hI I.mu0 _),
      chrG_eq (colLev I.Ch 0) _ _ (ClsZero.levelTypePrimes_stepZero_eq_colLev hI a _) (ClsZero.levelTypePrimes_stepZero_eq_colLev hI I.mu0 _) ga.2.1 gm.2.1 ek]

theorem mem_Fi_of_free {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) (hS : S.Free)
    (φ : S.Cl → Col2.Fr emb σ n → ℂ) : φ ∈ S.Fi emb σ lam ↔ ∀ c, φ c ∈ ValC (Gr emb σ n) lam := by
  constructor
  · intro h c
    exact (h c).1
  · intro h c
    refine ⟨h c, fun g => ?_⟩
    have hg : g.1 = 1 := hS c.1 g.1 _ g.2
    funext y
    show S.tr emb σ c.1 g.1 (φ c) y = φ c y
    rw [hg]
    simp [GStep.tr, trFr_apply, frMul_one]


set_option maxHeartbeats 1000000 in
theorem twAtT_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (a : I.ι), ∃ t : TwAtT (I.tw l l0 Z) u a, t.eVT = Equiv.refl _ ∧ ∀ v (r : 𝓞 B.host.E), t.eFv v (I.resT l u a v r) = I.resT l u I.mu0 (t.eVT v) r := by
  intro B X I hI hP l Z l0 u a
  refine ⟨
    { eVT := Equiv.refl _
      eFv := fun v => RingEquiv.refl _
      psiT := fun v x => rfl
      rhoT := by
        intro v x φ
        have e1 := dil_eCls0 B X I hI l u a v x
        have e2 := dilT_eCls0 B X I hI l u a v x
        funext c y
        obtain ⟨c', rfl⟩ := (I.eCls0 l u a).surjective c
        show (I.atIn u a).dilT B.fields.emb B.embLL 0 v x (I.eCls0 l u a c') (φ ((I.eCls0 l u a).symm ((I.atIn u a).dil 0 v x (I.eCls0 l u a c')))) y = (I.atIn u I.mu0).dilT B.fields.emb B.embLL 0 v x ((I.eCls0 l u a).symm (I.eCls0 l u a c')) (φ ((I.atIn u I.mu0).dil 0 v x ((I.eCls0 l u a).symm (I.eCls0 l u a c')))) y
        simp only [e1, e2, Equiv.symm_apply_apply]
      Mu0 := by
        show (I.stp u a 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0) = Submodule.map (LinearEquiv.funCongrLeft ℂ (Col2.Fr B.fields.emb B.embLL (B.R.N 0) → ℂ) (I.eCls0 l u a).symm).toLinearMap ((I.stp u I.mu0 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0))
        rw [Submodule.map_equiv_eq_comap_symm]
        ext ψ
        rw [Submodule.mem_comap, mem_Fi_of_free _ _ _ _ (l.lev u a).free0, mem_Fi_of_free _ _ _ _ (l.lev u I.mu0).free0]
        constructor
        · intro h c
          exact h _
        · intro h c
          obtain ⟨c', rfl⟩ := (I.eCls0 l u a).surjective c
          have := h c'
          simpa using this
      duStar := rfl
      Dstar := rfl
      GamP := rfl
      tauOf := fun w hw v => rfl
      seenP := fun w hw => rfl }, rfl, fun v r => rfl⟩

end GlobalTheory.Mem.Col2.TwAtStd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeValuesKilledByLoweringPart
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeValuesKilledByLoweringPart
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift.LowerKill

open GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

theorem entry_eq_zero {n : ℕ} {ε : Fin n → Bool} {κ : Matrix (Fin n) (Fin n) ℂ}
    (h : κ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ) {a b : Fin n} (hab : ε a ≠ ε b) : κ a b = 0 := by
  have e := congrFun (congrFun h a) b
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at hab e
  · simp only [Bool.false_eq_true, if_false, if_true] at e
    linear_combination (1 / 2 : ℂ) * e
  · simp only [Bool.false_eq_true, if_false, if_true] at e
    linear_combination (-1 / 2 : ℂ) * e

theorem block_conj {n : ℕ} {ε : Fin n → Bool} {κ κ' Y : Matrix (Fin n) (Fin n) ℂ}
    (h : κ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ) (h' : κ' * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * κ')
    (hY : ∀ a b, ¬ (ε a = false ∧ ε b = true) → Y a b = 0) (a b : Fin n) (hab : ¬ (ε a = false ∧ ε b = true)) :
    (κ' * Y * κ) a b = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : ε d = ε b
  · rw [Matrix.mul_apply, Finset.sum_eq_zero fun c _ => ?_, zero_mul]
    by_cases hc : ε a = ε c
    · rw [hY c d (by rw [← hc, hd]; exact hab), mul_zero]
    · rw [entry_eq_zero h' hc, zero_mul]
  · rw [entry_eq_zero h hd, mul_zero]

variable {D : D7} {T : HSp D} {Sp : D.what₂.Tau → SPar}

theorem frame_mem_UH (M : DSModel T Sp) (τ : D.what₂.Tau) {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hκ : κ ∈ Formalism.REAL.Kset (M.ε τ)) : (M.fr τ)⁻¹ * κ * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
  have hu : IsUnit (M.fr τ).det := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : κᴴ * κ = 1 := hκ.1.1
  have h2 : κᴴ * Formalism.REAL.Jm (M.ε τ) * κ = Formalism.REAL.Jm (M.ε τ) := by
    rw [Matrix.mul_assoc, ← hκ.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h3 : M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = κ * M.fr τ := by
    rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]
  show ((M.fr τ)⁻¹ * κ * M.fr τ)ᴴ * gramAt D T τ * ((M.fr τ)⁻¹ * κ * M.fr τ) = gramAt D T τ
  rw [← M.fr_gram τ]
  calc _ = (M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ))ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * ((M.fr τ)⁻¹ * κ * M.fr τ)) := by
        rw [conjTranspose_mul (M.fr τ)]
        simp only [Matrix.mul_assoc]
    _ = (M.fr τ)ᴴ * (κᴴ * Formalism.REAL.Jm (M.ε τ) * κ) * M.fr τ := by
        rw [h3, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h2]

theorem adAt_mem_pMinus {θ : InfFam D} (hθ : IsInfFam θ) (M : DSModel T Sp) (ρ τ : D.what₂.Tau)
    {κ : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hκ : κ ∈ Formalism.REAL.Kset (M.ε ρ))
    {Z : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hZ : Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ) :
    adAt θ (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) τ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ := by
  have hs := atTau_spec hθ T ρ (frame_mem_UH M ρ hκ)
  have hi : infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ)) *
      infMat D.sp.cm.sig T.gram (θ τ) (atTau θ T ρ ((M.fr ρ)⁻¹ * κ * M.fr ρ))⁻¹ = 1 := by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  unfold adAt
  by_cases c : τ = ρ
  · subst c
    have hu : IsUnit (M.fr τ).det := (isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have h1 : κ * κᴴ = 1 := hκ.1.2
    have h1' : κᴴ * κ = 1 := hκ.1.1
    have hJ : κᴴ * Formalism.REAL.Jm (M.ε τ) = Formalism.REAL.Jm (M.ε τ) * κᴴ := by
      have := congrArg conjTranspose hκ.2
      rw [conjTranspose_mul, conjTranspose_mul, Formalism.REAL.Jm_conjTranspose] at this
      exact this.symm
    rw [hs.2.1] at hi ⊢
    have hi2 : (M.fr τ)⁻¹ * κ * M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ) = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc _ κᴴ, mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_assoc,
        ← Matrix.mul_assoc κ, h1, Matrix.one_mul, nonsing_inv_mul _ hu]
    rw [← inv_eq_right_inv hi, inv_eq_right_inv hi2]
    intro a b hab
    have e : M.fr τ * ((M.fr τ)⁻¹ * κᴴ * M.fr τ * Z * ((M.fr τ)⁻¹ * κ * M.fr τ)) * (M.fr τ)⁻¹ =
        κᴴ * (M.fr τ * Z * (M.fr τ)⁻¹) * κ := by
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one, mul_nonsing_inv_cancel_left _ _ hu]
    rw [e]
    exact block_conj hκ.2 hJ hZ a b hab
  · rw [hs.2.2 τ c] at hi ⊢
    rw [Matrix.one_mul] at hi
    rw [hi, Matrix.one_mul, Matrix.mul_one]
    exact hZ

variable {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {θ : InfFam D}

theorem exists_op (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (Z : Matrix (Fin T.rank) (Fin T.rank) ℂ) : ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h,
      RderC θ T τ Z (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f) := by
  have key : ∀ X ∈ lieAt T τ, ∃ L : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → ∀ h,
      Rder θ T τ X (fun g => thetaKO om h g f) = fun g => thetaKO om h g (L f) := by
    intro X hX
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_weilDatum_generator_realOneParamGroup D ψ S T χS χT om hom θ hθ τ X hX
    refine ⟨L, fun f hf h => funext fun g => ?_⟩
    have := ((hL f hf).2.2.2 (h, g) 0).deriv
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
  obtain ⟨L₁, e1⟩ := key _ h1
  obtain ⟨L₂, e2⟩ := key _ h2
  refine ⟨L₁ + Complex.I • L₂, fun f hf h => ?_⟩
  unfold RderC
  rw [e1 f hf, e2 f hf]
  funext g
  simp [thetaKO]

def killed (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (M : DSModel T Sp) {Y : Type} [AddCommGroup Y]
    [Module ℂ Y] (pt : Y →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P)) : Submodule ℂ Y where
  carrier := {P | ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt P)) = 0}
  add_mem' := by
    intro P Q hP hQ τ Z hZ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h
    have b := hQ τ Z hZ h
    rw [hL _ (hpt _)] at a b ⊢
    funext g
    have a' := congrFun a g
    have b' := congrFun b g
    simp only [thetaKO, map_add (f := _), Pi.add_apply, Pi.zero_apply] at a' b' ⊢
    rw [a', b', add_zero]
  zero_mem' := by
    intro τ Z _ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    rw [hL _ (hpt _)]
    funext g
    simp [thetaKO]
  smul_mem' := by
    intro r P hP τ Z hZ h
    obtain ⟨L, hL⟩ := exists_op hom hθ τ Z
    have a := hP τ Z hZ h
    rw [hL _ (hpt _)] at a ⊢
    funext g
    have a' := congrFun a g
    simp only [thetaKO, map_smul, Pi.smul_apply, Pi.zero_apply] at a' ⊢
    rw [a', smul_zero]

theorem values_killed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt Δ)) = 0) → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ (v : ∀ ρ, lowT M ρ) w h, RderC θ T τ Z (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v) w))) = 0 := by
  intro D ψ S T χS χT om hom θ hθ Sp M h1 h2 c hc pt hpt Δ io hio hΔ τ Z hZ v w h
  classical
  obtain ⟨hS, hK, v₀, w₀, hv₀, hw₀, e₀⟩ := hio
  beta_reduce at hS hK
  let N := killed hom hθ M pt hpt
  have step1 : ∀ w, io (PiTensorProduct.tprod ℂ v₀) w ∈ N := by
    obtain ⟨-, -, -, -, -, -, -, hd, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ S hθ
    suffices hst : ∀ g, (N.comap (io (PiTensorProduct.tprod ℂ v₀))).map (c.ρ g) ≤
        N.comap (io (PiTensorProduct.tprod ℂ v₀)) by
      intro w
      refine (((hc.2.2.2.2 _ hst).resolve_left fun h0 => ?_).ge Submodule.mem_top :
        w ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)))
      have hm : w₀ ∈ N.comap (io (PiTensorProduct.tprod ℂ v₀)) := by
        show io (PiTensorProduct.tprod ℂ v₀) w₀ ∈ N
        rw [e₀]
        exact hΔ
      rw [h0, Submodule.mem_bot] at hm
      rw [hm, norm_zero] at hw₀
      exact zero_ne_one hw₀
    · rintro g _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, u, hu, rfl⟩ := hd g
      intro τ Z hZ h
      have e : (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v₀) (c.ρ (a * u) x)))) =
          fun g => thetaKO om (h * u) g (pt (io (PiTensorProduct.tprod ℂ v₀) x)) := by
        funext g
        rw [map_mul, hc.1 a ha, one_mul, ← hS u hu]
        unfold thetaKO
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
      rw [e]
      exact hx τ Z hZ (h * u)
  let B : MultilinearMap (RingHom.id ℂ) (fun τ => lowT M τ) (PolF D T.rank S.rank) :=
    (io.flip w).compMultilinearMap (PiTensorProduct.tprod ℂ)
  refine mem_of_translates h1 h2 B N v₀ (fun ρ h0 => ?_) (step1 w) ?_ v τ Z hZ h
  · have := hv₀ ρ
    rw [h0] at this
    simp at this
  · intro ρ k hk v u hu hv τ Z hZ h
    have e : (fun g => thetaKO om h g (pt (B (Function.update v ρ u)))) =
        rTr T (atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) fun g => thetaKO om h g (pt (B v)) := by
      funext g
      have := hK ρ k hk v u hu w
      show om (h, g) (pt (io (PiTensorProduct.tprod ℂ (Function.update v ρ u)) w)) 0 =
        om (h, g * atTau θ T ρ ((M.fr ρ)⁻¹ * k * M.fr ρ)) (pt (io (PiTensorProduct.tprod ℂ v) w)) 0
      rw [← this, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e, RderC_rTr hθ (isRealPt_atTau hθ ρ (frame_mem_UH M ρ hk)), hv τ _ (adAt_mem_pMinus hθ M ρ τ hk hZ) h]
    rfl

end GlobalTheory.DefLift.LowerKill

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeValuesKilledByLoweringPartStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_values_killed_by_loweringPart : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ h, RderC θ T τ Z (fun g => thetaKO om h g (pt Δ)) = 0) → ∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ (v : ∀ ρ, lowT M ρ) w h, RderC θ T τ Z (fun g => thetaKO om h g (pt (io (PiTensorProduct.tprod ℂ v) w))) = 0 := by
  first | exact @GlobalTheory.DefLift.LowerKill.values_killed | exact GlobalTheory.DefLift.LowerKill.values_killed | (intros; apply GlobalTheory.DefLift.LowerKill.values_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotTwistPlaceReferenceTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotTwistPlaceReferenceTuple
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem not_underQ_mu0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ v : HeightOneSpectrum (𝓞 B.host.F), ¬ I.UnderQ I.mu0 v := by
  intro B X I _ v ⟨P, hP, _⟩
  have e : P ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := I.twistPrimes_reference_tuple_eq_empty ▸ hP
  simp at e

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotTwistPlaceReferenceTupleStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_twistPlace_referenceTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → ∀ v : HeightOneSpectrum (𝓞 B.host.F), ¬ I.UnderQ I.mu0 v := by
  intro B X I _ v ⟨P, hP, _⟩
  have hEmpty : P ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) :=
    I.twistPrimes_reference_tuple_eq_empty ▸ hP
  simp at hEmpty
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOk
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 1600000 in
theorem laws_of_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.Laws := by
  intro B X I h
  have hch := GlobalTheory.T.trueColumn_chains_satisfy_conditions I h
  have hlev := GlobalTheory.T.levelPrimeData_ok_of_trueColumnChoices I h
  have hper := GlobalTheory.T.trueColumns_periodMapDatum_ok_and_over_levelPrime I h
  have hall := fun u a => laws_all (I.chIn u a) (I.atIn u a) B.fields.emb B.embLL (B.hcW u) (base_fOk B) (hch u a).1 (hlev u a)
    (I.perIn u a) (hper u a).1 B.places
  exact
    { pr := (base_fields_primes_ok B X).2.1
      ch := fun u a => (hch u a).1
      lev := hlev
      per := fun u a => (hper u a).1
      ovr := fun u a => (hper u a).2
      atL := fun u a => (hall u a).1
      fmL := fun u a => (hall u a).2
      xi0 := h.trueColumnChoices_heckeChar_reference_eq_one
      idx0 := fun a => (hch B.u₀ a).2.1
      bij0 := fun u a b => (GlobalTheory.T.cl0_bijective_and_deco_eq I h u a b).1
      lat := fun u a => (hch u a).2.2 }

end GlobalTheory.Mem.Col2.TC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldDegreeLeAndRootDiscrBound
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldDegreeLeAndRootDiscrBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.Fld.RaySize

theorem isEmpty_realEmb (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] : IsEmpty (E →+* ℝ) := by
  refine ⟨fun ψ => ?_⟩
  have h : InfinitePlace.IsReal (InfinitePlace.mk (Complex.ofRealHom.comp ψ)) :=
    ⟨_, ComplexEmbedding.isReal_iff.2 (by ext x; simp [ComplexEmbedding.conjugate]), rfl⟩
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)) h

theorem degOver_le_and_sz : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ) (N : ℕ) (M : IntermediateField ℚ ℂ) (h : IsRayFieldIn φ (natIdeal E N) M), N ≠ 0 → degOver φ M h.emb_mem ≤ classNumber E * N ^ Module.finrank ℚ E ∧ Sz M (Real.log (Module.finrank ℚ E) + Real.log (degOver φ M h.emb_mem)) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log N + Real.log (degOver φ M h.emb_mem)) := by
  intro E _ _ _ φ N M h hN
  haveI : NumberField M := h.numberField
  letI := algOf φ M h.emb_mem
  have hR : IsRayField E M (natIdeal E N) := h.isRayField
  haveI : IsAbelianGalois E M := hR.1
  have hdeg : degOver φ M h.emb_mem = Module.finrank E M := rfl
  have hfin := finrank_mul_degOver φ M h.emb_mem
  rw [hdeg] at hfin ⊢
  refine ⟨?_, ?_⟩
  · have h1 := GlobalTheory.FieldSize.RayDegree.finrank_le E M (natIdeal E N) (natIdeal_ne_bot hN) hR.2
    haveI := isEmpty_realEmb E
    rwa [Fintype.card_eq_zero, pow_zero, mul_one, Ideal.absNorm_span_natCast, RingOfIntegers.rank] at h1
  · refine ⟨inferInstance, ?_, ?_⟩
    · rw [← hfin]
      have : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
      have : (0 : ℝ) < Module.finrank E M := by exact_mod_cast Module.finrank_pos
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    · have hun : ∀ 𝔭 : HeightOneSpectrum (𝓞 E), (N : 𝓞 E) ∉ 𝔭.asIdeal → GlobalTheory.NT.UnramIn M 𝔭 :=
        fun 𝔭 h𝔭 => hR.2.1 𝔭 (fun hd => h𝔭 (Ideal.dvd_span_singleton.1 hd))
      have hmem := GlobalTheory.DifferentBound.natCast_mul_finrank_mem_differentIdeal E M N (Nat.pos_of_ne_zero hN) hun
      have h2 := GlobalTheory.log_rootDiscr_le_of_natCast_mem_differentIdeal E M (N * Module.finrank E M)
        (Nat.mul_pos (Nat.pos_of_ne_zero hN) Module.finrank_pos) hmem
      have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
      have hd : (0 : ℝ) < Module.finrank E M := by exact_mod_cast Module.finrank_pos
      rw [Nat.cast_mul, Real.log_mul hN'.ne' hd.ne', ← add_assoc] at h2
      exact h2

end GlobalTheory.Mem.Fld.RaySize
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassFieldDegreeLeAndRootDiscrBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_degree_le_and_rootDiscrBound : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (φ : E →+* ℂ) (N : ℕ) (M : IntermediateField ℚ ℂ) (h : IsRayFieldIn φ (natIdeal E N) M), N ≠ 0 → degOver φ M h.emb_mem ≤ classNumber E * N ^ Module.finrank ℚ E ∧ Sz M (Real.log (Module.finrank ℚ E) + Real.log (degOver φ M h.emb_mem)) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + Real.log N + Real.log (degOver φ M h.emb_mem)) := by
  first | exact @GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz | exact GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz | (intros; apply GlobalTheory.Mem.Fld.RaySize.degOver_le_and_sz <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterTypePrimesValuesCoefficientFiel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterTypePrimesValuesCoefficientFiel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.PsiRat

theorem natCast_resField_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))
    (a := (p : v.adicCompletionIntegers F))).2 ?_
  have h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F) := by
    simp
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h
  exact h2.trans_lt h3

theorem range_of_pow_g (B : Base) (i : Fin 2) (z : ℂ) (hz : z ^ B.host.g i = 1) : ∃ r : B.LL, B.embLL r = z := by
  have hp := B.host.g_prime i
  obtain ⟨ζ, -, hζ⟩ := B.roots_Ks (B.host.g i * (B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : B.host.g i * (B.host.g i - 1) ≠ 0 := mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim := Complex.isPrimitiveRoot_exp _ hne
  have : NeZero (B.host.g i * (B.host.g i - 1)) := ⟨hne⟩
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one (ξ := z) (by rw [pow_mul, hz, one_pow])
  exact ⟨ζ ^ k, by rw [map_pow, hζ, hk]⟩

end GlobalTheory.Mem.Col2.TC.PsiRat


open GlobalTheory.Mem.Col2.TC.PsiRat in
theorem GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  intro B X I _ _ l Z G _ j v h x
  refine range_of_pow_g B j _ ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have h0 := natCast_resField_eq_zero _ v _ h
  erw [h0]
  rw [zero_mul, AddChar.map_zero_eq_one]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterTypePrimesValuesCoefficientFielStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psi0_eq_embLL : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g), I.IdG l Z G → ∀ j v h x, ∃ r : B.LL, B.embLL r = G.psi0 j v h x := by
  first | exact @GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField | exact GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField | (intros; apply GlobalTheory.Mem.Col2.TC.additiveCharacter_typePrimes_values_coefficientField <;> assumption)
end
end
