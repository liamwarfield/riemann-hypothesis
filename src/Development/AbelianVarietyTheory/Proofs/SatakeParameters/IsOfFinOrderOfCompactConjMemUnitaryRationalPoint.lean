module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnipotentLevelNilpotent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotDvdCardStabFrm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPoint
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory

theorem isOfFinOrder_of_conj_mem_ratU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Subgroup (UA E n)),
    IsCompact (D : Set (UA E n)) → ∀ (g : UA E n), ∀ c ∈ D, g * c * g⁻¹ ∈ ratU E n → IsOfFinOrder c := by
  intro E _ _ _ n D hD g c hc hgc
  haveI : T1Space (GA E n) := by
    set_option synthInstance.maxHeartbeats 200000 in
      infer_instance
  haveI : DiscreteTopology (ratGL E n).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n
  have hcl : IsClosed (((ratGL E n).range : Subgroup (GA E n)) : Set (GA E n)) := Subgroup.isClosed_of_discrete
  let K : Set (GA E n) := (fun x : UA E n => ((g * x * g⁻¹ : UA E n) : GA E n)) '' (D : Set (UA E n))
  have hK : IsCompact K := hD.image (continuous_subtype_val.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hKG : IsCompact (K ∩ ((ratGL E n).range : Set (GA E n))) := hK.inter_right hcl
  let t : Set (ratGL E n).range := {x | (x : GA E n) ∈ K}
  have himg : Subtype.val '' t = K ∩ ((ratGL E n).range : Set (GA E n)) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
    · rintro ⟨hy, hy'⟩; exact ⟨⟨y, hy'⟩, hy, rfl⟩
  have ht : IsCompact t := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]; exact hKG
  have hfin : (K ∩ ((ratGL E n).range : Set (GA E n))).Finite := by
    rw [← himg]; exact (ht.finite_of_discrete).image _
  by_contra hno
  have hinj := (injective_pow_iff_not_isOfFinOrder).2 hno
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((g * c ^ k * g⁻¹ : UA E n) : GA E n)) ?_ ?_ hfin
  · intro i j hij
    apply hinj
    have h1 : g * c ^ i * g⁻¹ = g * c ^ j * g⁻¹ := Subtype.ext hij
    simpa using h1
  · intro k
    refine ⟨⟨c ^ k, D.pow_mem hc k, rfl⟩, ?_⟩
    have hk : g * c ^ k * g⁻¹ ∈ ratU E n := by
      have := (ratU E n).pow_mem hgc k
      simpa [conj_pow] using this
    exact (Subgroup.mem_subgroupOf).1 hk

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPointStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOfFinOrder_of_compact_conj_mem_unitaryRationalPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Subgroup (UA E n)), IsCompact (D : Set (UA E n)) → ∀ (g : UA E n), ∀ c ∈ D, g * c * g⁻¹ ∈ ratU E n → IsOfFinOrder c := by
  first | exact @GlobalTheory.isOfFinOrder_of_conj_mem_ratU | exact GlobalTheory.isOfFinOrder_of_conj_mem_ratU | (intros; apply GlobalTheory.isOfFinOrder_of_conj_mem_ratU; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralOffPrimesMatrixStepEntryData
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralOffPrimesMatrixStepEntryData
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.KerTie

theorem intOff_pow' {S : Finset ℕ} {z : ℂ} (h : IntOff S z) (n : ℕ) : IntOff S (z ^ n) := by
  induction n with
  | zero => simpa using IntOff.one
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem intOff_prod' {S : Finset ℕ} {κ : Type} (s : Finset κ) (f : κ → ℂ) (h : ∀ k ∈ s, IntOff S (f k)) :
    IntOff S (∏ k ∈ s, f k) :=
  Finset.prod_induction _ (IntOff S) (fun _ _ ha hb => ha.mul hb) IntOff.one h

theorem intAt_chArg_of_omPhi {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}
    (hL : L.Ok Ch sel mu cst G m2) {i : ℕ} (hi : i < m2) (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu)
    {y : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))}
    (h0 : omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) y ≠ 0) :
    IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * -Loc.chArg y) := by
  have hm := hL.hm
  by_cases hP : P.1 ∈ Pr.vGs
  · have h1 := (GlobalTheory.Mem.Col2.BddG.omPhi_bdd_type Ch sel mu cst i P (by omega) hP _ _ (hL.stabG i al P hP)
      (hL.stabG (i + 1) be P hP)).2 y h0
    rw [hL.depthG P hP, pow_one, mul_neg]
    exact GlobalTheory.TopStep.intAt_neg h1
  · have h1 := right_ne_zero_of_mul h0
    rw [PhiAt, if_neg hP] at h1
    have hb := hL.boundQ i al P hP
    have hb' := hL.boundQ (i + 1) be P hP
    have hD := hL.depthQ' P hP
    simp only [lamYat, hP, if_false, GlobalTheory.GO.ChRoot.mem_lamY_zero] at hb hb'
    have hint : IntAt P.1 ((qOf P.1 : X.E) ^ (i + 1) * Loc.chArg y) := by
      refine GlobalTheory.ColPeriod.EntQ.intAt_chArg _ y fun v hv => ?_
      have h2 := (hb' _ (GlobalTheory.ColPeriod.EntQ.int_of_PhiQ (GlobalTheory.ColPeriod.EntQ.k_le_N R _) (GlobalTheory.ColPeriod.EntQ.k_le_N R _) h1 (hb v hv).1)).2
      have h3 : (L.h i al P) ((L.h i al P)⁻¹ v) = v := LinearEquiv.apply_symm_apply _ v
      simpa [h3] using h2
    obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + (i + 1) := ⟨cst.D P - (i + 1), by omega⟩
    rw [hd, pow_add, mul_neg, mul_assoc]
    exact GlobalTheory.TopStep.intAt_neg ((GlobalTheory.TopStep.intAt_pow (GlobalTheory.TopStep.intAt_nat _) _).mul hint)

theorem intOff_xiEntry : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < t.m2 → ∀ al be p p' x, IntOff (t.O u μ).S (t.seam.σ₀ (XiEntry (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i al be p p' x)) := by
  intro D L hT Gi Gl K Y cX ex t hmu hval u μ hg i hi al be p p' x
  have hL := t.idx_ok μ
  have hm := hL.hm
  unfold XiEntry
  rw [map_mul, map_prod]
  refine IntOff.mul ?_ (intOff_prod' _ _ fun P _ => ?_)
  · unfold phiT
    split_ifs
    · simpa using IntOff.one
    · simpa using IntOff.zero
  · have hq := GlobalTheory.KerTie.sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P
    have hst : P.1 ∈ t.Pr.vGs → (t.idx μ).h i al P ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) i P.1) ∧
        (t.idx μ).h (i + 1) be P ∈ stabL t.X.E _ (lamYat (Pr := t.Pr) (i + 1) P.1) :=
      fun hP => ⟨hL.stabG i al P hP, hL.stabG (i + 1) be P hP⟩

    have hom : ∀ y, IntOff (t.O u μ).S (t.seam.σ₀ (omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P
        ((t.idx μ).h i al P) ((t.idx μ).h (i + 1) be P) y)) := fun y =>
      GlobalTheory.T.integralAwayFrom_moved_localDatum D L hT Gi Gl K Y cX ex t hmu hval u μ hg i (by omega) P _ _ hst y
    unfold XiAt E1at Loc.E1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_mul, map_sum]
    refine IntOff.mul (GlobalTheory.UnipVol.intOff_volN_Cbe D L hT Gi Gl K Y cX ex t u μ i P _) (IntOff.mul ?_ (IntOff.sum _ _ fun s _ => ?_))
    · rw [map_pow, map_inv₀, map_pow, map_natCast, ← inv_pow]
      exact intOff_pow' (intOff_pow' (IntOff.inv_nat hq) _) _
    · generalize Loc.xx1 _ s = y
      by_cases h0 : omPhi t.Ch t.sel (t.tup μ) (t.cst μ) i P ((t.idx μ).h i al P) ((t.idx μ).h (i + 1) be P) y = 0
      · rw [h0, zero_mul, map_zero]
        exact IntOff.zero
      · rw [map_mul]
        refine (hom _).mul (IntOff.of_pow (n := qOf P.1 ^ (t.cst μ).D P) (pow_pos (GlobalTheory.GO.ChRoot.qOf_pos _) _) ?_)
        rw [← map_pow, GlobalTheory.GO.ChRoot.psi_root hL.cst_ok P _ (intAt_chArg_of_omPhi hL hi al be P h0), map_one]

end GlobalTheory.KerTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralOffPrimesMatrixStepEntryDataStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralOffPrimes_matrixStepEntryData : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < t.m2 → ∀ al be p p' x, IntOff (t.O u μ).S (t.seam.σ₀ (XiEntry (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i al be p p' x)) := by
  first | exact @GlobalTheory.KerTie.intOff_xiEntry | exact GlobalTheory.KerTie.intOff_xiEntry | (intros; apply GlobalTheory.KerTie.intOff_xiEntry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceDualExpansionOrbitLength
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceDualExpansionOrbitLength
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.TrDualExpand

variable {K : Type} [Field K]

theorem iter_mul (σ : K →+* K) (n : ℕ) (a b : K) : σ^[n] (a * b) = σ^[n] a * σ^[n] b := by
  rw [← RingHom.coe_pow, map_mul]

theorem sum_zmod_val {d : ℕ} [NeZero d] (F : ℕ → K) :
    ∑ s : ZMod d, F s.val = ∑ n ∈ Finset.range d, F n := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_bijective (fun s : ZMod d => (⟨s.val, ZMod.val_lt s⟩ : Fin d))
    ⟨fun a b h => ZMod.val_injective d (by simpa using congrArg Fin.val h),
     fun i => ⟨(i.val : ZMod d), by ext; simp [ZMod.val_natCast_of_lt i.2]⟩⟩ _ _ (fun _ => rfl)

theorem sum_range_even (m : ℕ) (G : ℕ → K) :
    ∑ n ∈ Finset.range (2 * m), (if n % 2 = 0 then G n else 0) = ∑ i ∈ Finset.range m, G (2 * i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, if_pos (by omega), if_neg (by omega), add_zero]

theorem even_case {m d : ℕ} [NeZero d] (hd : 2 * m = d) (σ : K →+* K) (om oms : Fin m → K)
    (h : ∀ r r' : Fin m, (∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (om r * oms r') else 0) =
      if r = r' then 1 else 0) (i j : Fin m) :
    ∑ k, σ^[2 * i.val] (om k) * σ^[2 * j.val] (oms k) = if i = j then 1 else 0 := by
  let M : Matrix (Fin m) (Fin m) K := fun i k => σ^[2 * i.val] (om k)
  let Q : Matrix (Fin m) (Fin m) K := fun i k => σ^[2 * i.val] (oms k)
  have hMQ : M.transpose * Q = 1 := by
    ext r r'
    rw [Matrix.mul_apply, Matrix.one_apply, ← h r r',
      sum_zmod_val (fun n => if n % 2 = 0 then σ^[n] (om r * oms r') else 0), ← hd, sum_range_even,
      ← Fin.sum_univ_eq_sum_range (fun i => σ^[2 * i] (om r * oms r'))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [iter_mul]
    rfl
  have hMQ' : M * Q.transpose = 1 := by
    have := congrArg Matrix.transpose (mul_eq_one_comm.1 hMQ)
    simpa [Matrix.transpose_mul] using this
  have := congrFun (congrFun hMQ' i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

theorem sum_eq_ite {d : ℕ} [NeZero d] (σ : K →+* K) (om oms : Fin (d / 2) → K)
    (hT : TrDual d σ om oms) (s t : ZMod d) (hst : s.val % 2 = t.val % 2) :
    ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0 := by
  obtain ⟨hc, h⟩ := hT
  rw [Fintype.card_fin] at hc
  have hs := ZMod.val_lt s
  have ht := ZMod.val_lt t
  let i : Fin (d / 2) := ⟨s.val / 2, by omega⟩
  let j : Fin (d / 2) := ⟨t.val / 2, by omega⟩
  have E := even_case hc σ om oms h i j
  have hij : (i = j) ↔ (s = t) := by
    rw [Fin.ext_iff, ← (ZMod.val_injective d).eq_iff]
    simp only [i, j]
    omega
  rcases Nat.mod_two_eq_zero_or_one s.val with h0 | h1
  · have e1 : s.val = 2 * i.val := by simp only [i]; omega
    have e2 : t.val = 2 * j.val := by simp only [j]; omega
    rw [e1, e2, E]
    exact if_congr hij rfl rfl
  · have e1 : s.val = 2 * i.val + 1 := by simp only [i]; omega
    have e2 : t.val = 2 * j.val + 1 := by simp only [j]; omega
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [e1, e2, Function.iterate_succ_apply', ← map_mul, ← map_sum, E]
    split_ifs with h3 h4 h4
    · exact map_one σ
    · exact absurd (hij.1 h3) h4
    · exact absurd (hij.2 h4) h3
    · exact map_zero σ

end GlobalTheory.TrDualExpand

namespace GlobalTheory.KerStd.HypCoord

theorem trDual_expand : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p),
    TrDual (nP D p) σ om oms → ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 →
      ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0 :=
  fun _ _ _ σ om oms hT s t hst => GlobalTheory.TrDualExpand.sum_eq_ite σ om oms hT s t hst

end GlobalTheory.KerStd.HypCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceDualExpansionOrbitLengthStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceDual_expansion_orbitLength : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p), TrDual (nP D p) σ om oms → ∀ s t : ZMod (nP D p), s.val % 2 = t.val % 2 → ∑ k, σ^[s.val] (om k) * σ^[t.val] (oms k) = if s = t then 1 else 0 := by
  first | exact @GlobalTheory.KerStd.HypCoord.trDual_expand | exact GlobalTheory.KerStd.HypCoord.trDual_expand | (intros; apply GlobalTheory.KerStd.HypCoord.trDual_expand <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRatIdxOfJetsRatDeg
noncomputable section

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recWts recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator (FnModAt FnMod facTop facPen Zmu)
open GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance (DegOneUnram)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat InDeg HAt LatWithBasis)

def JetLossAllAt {X : Fields} (Pr : Primes X) (R : Ranks) (A : Amb X)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) : Prop :=
  ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)), ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal →
  ∀ (u : Pr.Word) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok →
  ∀ (j b : ℕ), j < R.m → b = R.N (j + 1) →
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))) (N' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N → IsSdLat N' → StdOver (Pr.g i) N → StdOver (Pr.g i) N' →
  ∀ Ξ : HomE X.E (R.N j) b → X.K, DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w N N' Ξ →
  ∀ e : DVar X.Tau (R.N j) b →₀ ℕ, e.degree + 1 < Pr.g i →
    (∀ c : ℕ, 0 < c → c ∣ cAof sel mu cst * cBof sel mu cst u → e ∈ RatIdx A (Sall sel mu u) (cAof sel mu cst) c N N' Ξ) →
    w.valuation X.K ((Pr.g i : X.K) ^ (X.f * R.N j * b) *
      (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) *
      jetSum A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N N' Ξ e) ≤ 1

def JetLossAll (D : D7) (EX : ErrX D) (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E))
    {δ : ℂ} (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) : Prop :=
  HostTie EX → IsSel (recFields D) sel → AnTie D δ χ cD →
    JetLossAllAt (recPrimes EX) D.R (ambOf (recSeam D) B χ cD) sel (badS D)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

section
variable (A : Amb X)

theorem kerOf_bound_all (hJ : JetLossAllAt Pr R A sel S) (hO : JetOpWeyl) (hW : ChainWeights) (hPr : Pr.Ok)
    (hc : cst.Ok) (u : Pr.Word) (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    {j j' : ℕ} (hj : j < R.m) (hj' : j' = j + 1)
    (hscal : ∀ (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)) (fr : Frs X.E n (rowSG Pr sel mu)),
      IsSdLat N → StdOver (Pr.g i) N → IsFrames N fr →
      w.valuation X.K (muInvDet sel (rowSG Pr sel mu) (mUof Ch mu j) (muAt Ch sel mu cst j) N fr) = 1)
    (hdeg : (∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a) + 1 < Pr.g i)
    (hrat : GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.JetsRatDeg A (R.N j) (R.N (j + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      fun τ => ∑ a, (W.nuW u (j + 1) τ).w a)
    {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := SG)) (d' : DecoSet (E := X.E) (n := R.N j') (ST := Pr.vT u) (SG := SG'))
    (hs : StdOver (Pr.g i) d.1.N) (hs' : StdOver (Pr.g i) d'.1.N) {fr : Frs X.E (R.N j) (rowSG Pr sel mu)}
    {fr' : Frs X.E (R.N j') (rowSG Pr sel mu)} (hf : IsFrames d.1.N fr) (hf' : IsFrames d'.1.N fr')
    {Ξ : HomE X.E (R.N j) (R.N j') → X.K}
    (hΞ : DatumAt (Pr.vG i) (Sall sel mu u) (Pr.g i) (cBof sel mu cst u) w d.1.N d'.1.N Ξ)
    {v : Formalism.L2.DIV.VV X.K (W.lamTrue u j)} (hv : v ∈ localization₂ w.asIdeal (delAtr X.emb (W.lamTrue u j) d.1.Lsh)) :
    lossAt W i u j • kerOf (stepC W Ch sel mu cst A u j (W.lamTrue u j')) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
      d.1.N fr d'.1.N fr' Ξ v ∈ localization₂ w.asIdeal (delAtr X.emb (W.lamTrue u j') d'.1.Lsh) := by
  classical
  subst hj'
  have hT : ∀ Q ∈ Pr.vT u, ((Pr.g i : ℕ) : 𝓞 X.E) ∉ Q.asIdeal := fun Q hQ h =>
    natCast_notMem_of_ne (hPr.T_prime u) (hPr.g_prime i) (hPr.T_ne_g u i) _ h (T_mem_of_piT_mem hPr u (mem_divs hQ))
  have hsd : IsSdLat d.1.N := ⟨d.2.lat, d.2.uni⟩
  have hsd' : IsSdLat d'.1.N := ⟨d'.2.lat, d'.2.uni⟩
  rw [(GlobalTheory.GO.use₃ _ hT d w hw).2] at hv
  rw [(GlobalTheory.GO.use₃ _ hT d' w hw).2, stepC,
    kerOf_thDistC A _ _ (cAof_pos sel mu cst) (cBof_pos sel mu cst hPr u) _ _ _ _ _ _ d.2.lat d'.2.lat,
    LinearMap.smul_apply, smul_comm]
  refine smul_mem_localizationAt_of_le w _ ?_ ?_
  · rw [map_mul, map_inv₀, hscal _ _ _ hsd hs hf, hscal _ _ _ hsd' hs' hf', inv_one, one_mul]
  obtain ⟨s, s', hwt, hnu⟩ := hW X Pr R W u j hj
  refine hO X.K w X.Tau _ _ _ _ _ s s' _ hwt _ _
    (fun τ => (GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ _ (Formalism.L2.Ker.full_of_sd hsd)).toIsLattice)
    (fun τ => (GlobalTheory.TauLat.tauLatLattice X.E X.K X.Tau _ X.emb τ _ (Formalism.L2.Ker.full_of_sd hsd')).toIsLattice)
    (latWithBasis_of_stdOver X.emb (hPr.g_prime i).ne_zero d.2.lat hs w hw)
    (latWithBasis_of_stdOver X.emb (hPr.g_prime i).ne_zero d'.2.lat hs' w hw) _ _ (fun e he => ?_) v hv
  · have h1 : ∀ τ, ((∑ β, ∑ α, e (τ, β, α) : ℕ) : ℤ) = ∑ a, (W.nuW u (j + 1) τ).w a := fun τ => by
      rw [he τ]
      exact Finset.sum_congr rfl fun a _ => hnu τ a
    have h2 : (e.prod fun k n => X.emb k.1 (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ n) =
        ∏ τ, X.emb τ (star ((Pr.piG i : 𝓞 X.E) : X.E)) ^ (∑ a, (W.nuW u (j + 1) τ).w a).toNat := by
      rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun τ _ => ?_
      dsimp only
      rw [← h1 τ, Int.toNat_natCast, Finset.prod_pow_eq_pow_sum, Fintype.sum_prod_type]
    have h3 : e.degree + 1 < Pr.g i := by
      have h4 : (e.degree : ℤ) = ∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a := by
        rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type, Nat.cast_sum]
        exact Finset.sum_congr rfl fun τ _ => by rw [← h1 τ, Fintype.sum_prod_type]
      omega
    rw [lossAt, ← h2]
    refine hJ i w hw u mu cst hc j _ hj rfl _ _ hsd hsd' hs hs' Ξ hΞ e h3 fun c hc0 hdvd x hx _ => ?_
    refine hrat _ _ _ x ⟨hsd, hsd', hc0, hdvd, ?_⟩ e fun τ => ?_
    · change ((cAof sel mu cst * cBof sel mu cst u : ℕ) : 𝓞 X.E) • x ∈ homAt _ _ _
      rw [Nat.cast_mul, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hx
    · dsimp only
      rw [← h1 τ]
      have h5 : (∑ β, ∑ α, (e (τ, β, α) : ℤ)) = ((∑ β, ∑ α, e (τ, β, α) : ℕ) : ℤ) := by
        push_cast
        rfl
      convert (GlobalTheory.ColPeriodCompare.deg_eq e τ).trans h5

end

variable (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Amb X)


set_option maxHeartbeats 1000000 in
theorem colMu_bound_all (hJ : JetLossAllAt Pr R A sel S) (hO : JetOpWeyl) (hW : ChainWeights) (hM : StdMove)
    (hLP : LevelPrimes) (hSU : ScalarUnit) (hEG : EntryAtG) (hEQ : EntryAtQ) (hTQ : TopAtQ)
    (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hS : Pr.T u ∈ S) (hSg : ∀ i, Pr.g i ∈ S)
    {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2) {e : Fin R.m → X.Tau → ℚ} {eta : Formalism.L2.Host.HChar X.E}
    (hT : Ch.Tied G.σ₀ e G.mu0 eta) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (hK : KerEquivC W Ch sel mu cst L A u m2 b hY P) (hF : ∀ j, (chF W sel mu L u j).Ok)
    (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.K)) (hw : ((Pr.g i : ℕ) : 𝓞 X.K) ∈ w.asIdeal)
    (hwt : ∀ j ≤ R.m, ∀ b, WtUnit w ((chF W sel mu L u j).mem b))
    (hdeg : ∀ j < R.m, (∑ τ, ∑ a, (W.nuW u (j + 1) τ).w a) + 1 < Pr.g i)
    (hrat : ∀ j < R.m, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.JetsRatDeg A (R.N j) (R.N (j + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      fun τ => ∑ a, (W.nuW u (j + 1) τ).w a)
    (φ : MfV W Ch u) (hφ : φ ∈ MfL W Ch u) (d : (evGSD W Ch sel mu P u).D) :
    (∏ j ∈ Finset.range R.m, lossAt W i u j) • (colMu W Ch sel mu cst L A u m2 b hY P hK hF hL φ).1 d ∈
      localization₂ w.asIdeal ((evGSD W Ch sel mu P u).Del d) := by
  have hm := hL.hm
  have hlp := hLP X Pr sel S mu hX hPr hsel
  have hq : ∀ Q : rowSG Pr sel mu, Q.1 ∉ Pr.vGs → ((qOf Q.1 : ℕ) : 𝓞 X.K) ∉ w.asIdeal := fun Q hQ =>
    natCast_notMem_of_ne (hlp Q).1.1 (hPr.g_prime i) (fun h => (hlp Q).2 hQ (h ▸ hSg i)) w hw
  have hsu := hSU X Pr R Ch sel S mu cst L G m2 e eta hX hPr hsel hSg hT hL i w hw
  have heq := fun (Q : rowSG Pr sel mu) (hQ : Q.1 ∉ Pr.vGs) => hEQ X Pr R Ch sel S mu cst L G m2 hL Q w hQ (hlp Q).1 (hq Q hQ)
    fun j hj => (hsu j hj).1 Q fun h => hQ (vG_subset i h)
  have hcd := GlobalTheory.LastSteps.chainDataGuarded X Pr R Ch sel S mu cst m2 hPr hL.cst_ok hm
  rw [show Finset.range R.m = Finset.range (m2 + 2) by rw [hm]]
  refine colCpl_bound (chKerC W Ch sel mu cst L A u m2 b hY P hK).kk hF (fun j hj b => hwt j (by omega) b)
    (lossAt W i u) (chKerC W Ch sel mu cst L A u m2 b hY P hK).cp (hF (m2 + 1) b) (hwt _ (by omega) b)
    (fun j hj al be p p' => ?_) (fun al p₀ p Y hYm => ?_) (fun al p d₁ Y hYm => ?_) (startC hL u φ)
    (fun b' p => GlobalTheory.TestLat.WeylLocal.le_locP w _ (hφ (DecoF.deco p))) d
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u j al p
    obtain ⟨g', hg'⟩ := exists_std_pt W sel mu L hM hPr i u (j + 1) be p'
    refine Bd.transfer g g' ((hF j al).del_smul g p) ((hF (j + 1) be).del_smul g' p')
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j al be).equiv g g' p p') ?_
    generalize g • p = p, g' • p' = p' at hg hg' ⊢
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).kk j al be).k p p' =
        matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) j al be p p' := by
      simp only [chKerC, chKer, dif_pos hj]
    rw [e1]
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (by omega) rfl (hsu j (by omega)).2
      (hdeg j (by omega)) (hrat j (by omega)) (DecoF.deco p) (DecoF.deco p') hg hg' (isFrames_frsF p)
      (isFrames_frsF p') ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p).1 (DecoF.deco p').2
      (fun Q x => XiAt Ch sel mu cst j Q (L.h j al Q) (L.h (j + 1) be Q) (inFr (frsF sel mu p Q) (frsF sel mu p' Q) x))
      (fun Q hQ => fnModAt_inFr (isFrames_frsF p Q) (isFrames_frsF p' Q)
        (hEG X Pr R Ch sel S mu cst L G m2 hL j hj al be Q hQ (hlp Q).1))
      (fun Q hQ => awayAt_inFr (isFrames_frsF p Q) (isFrames_frsF p' Q) ((heq Q hQ).1 j hj al be))
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u m2 al p₀
    obtain ⟨g', hg'⟩ := exists_std_pt W sel mu L hM hPr i u (m2 + 1) b p
    refine Bd.transfer g g' ((hF m2 al).del_smul g p₀) ((hF (m2 + 1) b).del_smul g' p)
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).equiv1 g g' p₀ p Y) ?_
    have hY' := ((ybCpl W sel mu cst L u m2 b hY).equiv g' p Y).2 hYm
    suffices key : ∀ (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) Y',
        StdOver (Pr.g i) (DecoF.deco p₀).1.N → StdOver (Pr.g i) (DecoF.deco p).1.N → Y' ∈ ybSet sel mu cst (DecoF.deco p).1.N →
        Bd w (lossAt W i u m2) (((chF W sel mu L u m2).mem al).Del p₀) (((chF W sel mu L u (m2 + 1)).mem b).Del p)
          (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k1 p₀ p Y') from key _ _ _ hg hg' hY'
    intro p₀ p Y' hg hg' hY''
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k1 p₀ p Y' =
        cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p₀ p Y' := rfl
    rw [e1, cp1K, if_pos hY'']
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (by omega) rfl (hsu m2 (by omega)).2
      (hdeg m2 (by omega)) (hrat m2 (by omega)) (DecoF.deco p₀) (DecoF.deco p) hg hg' (isFrames_frsF p₀)
      (isFrames_frsF p) ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p₀).1 (DecoF.deco p).2 (facPen Ch sel mu cst L m2 al p₀ p Y')
      (fun Q hQ => (hcd Q hQ).2.2.2.1 L al (hL.stabG m2 al Q hQ) u p₀ p Y' hY'')
      (fun Q hQ => awayAt_inFr (isFrames_frsF p₀ Q) (isFrames_frsF p Q) ((heq Q hQ).2 al _))
  · obtain ⟨g, hg⟩ := exists_std_pt W sel mu L hM hPr i u (m2 + 1) b p
    obtain ⟨γ, hγ⟩ := hM X Pr hPr i _ d₁.1.N ⟨d₁.2.lat, d₁.2.uni⟩
    refine Bd.transfer (S' := evGSD W Ch sel mu P u) g (γ, 1) ((hF (m2 + 1) b).del_smul g p)
      (evGSD_del_smul W Ch sel mu hPr hsel u hS P γ d₁)
      (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).equiv2 g (γ, 1) p Y d₁) ?_
    have hY' := ((ybCpl W sel mu cst L u m2 b hY).equiv g p Y).2 hYm
    have hγ' : StdOver (Pr.g i) (((γ, 1) : (evGSD W Ch sel mu P u).G) • d₁).1.N := hγ
    suffices key : ∀ (p : ChPt (R := R) sel mu u (m2 + 1)) Y' (d₂ : RowPt Pr R sel mu),
        StdOver (Pr.g i) (DecoF.deco p).1.N → Y' ∈ ybSet sel mu cst (DecoF.deco p).1.N → StdOver (Pr.g i) d₂.1.N →
        Bd w (lossAt W i u (m2 + 1)) (((chF W sel mu L u (m2 + 1)).mem b).Del p) ((evGSD W Ch sel mu P u).Del d₂)
          (((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k2 p Y' d₂) from key _ _ _ hg hY' hγ'
    intro p Y' d₂ hg hY'' hγ'
    have e1 : ((chKerC W Ch sel mu cst L A u m2 b hY P hK).cp al).k2 p Y' d₂ =
        cp2K W Ch sel mu cst (chTh W Ch sel mu cst A u m2) p Y' d₂ := rfl
    rw [e1, cp2K, if_pos hY'']
    intro v hv
    refine kerOf_bound_all W Ch sel mu cst A hJ hO hW hPr hL.cst_ok u i w hw (j := m2 + 1) (j' := R.m) (by omega) hm
      (hsu _ (by omega)).2 (hdeg _ (by omega)) (hrat _ (by omega)) (DecoF.deco p) (tilQ sel mu u d₂) hg
      (stdOver_tilH _ (conj_piT_notMem hPr u) (piT_notMem_rowSG sel mu hPr hsel u hS) d₂ hγ') (isFrames_frsF p)
      (isFrames_frsT d₂) ?_ hv
    exact datumAt_prod hPr hL.cst_ok u i w (DecoF.deco p).1 (tilQ sel mu u d₂).2 (facTop Ch sel mu cst m2 p Y' d₂)
      (fun Q hQ => (hcd Q hQ).2.2.2.2 u (piT_notMem_rowSG sel mu hPr hsel u hS) p d₂ Y' hY'')
      (fun Q hQ => hTQ X Pr R Ch sel S mu cst L G m2 u hPr hsel hS hL Q w hQ (hlp Q).1 (hq Q hQ) p d₂ Y' hY'')

end GlobalTheory.ColPeriod
end
end
