module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetsRightTranslateInFramesTypePrime

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open NumberField IsDedekindDomain GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.FinPl ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_unif (q : Unif k) {x : k} (hx : valuation k x < 1) :
    valuation k x ≤ valuation k ((q.1 : 𝒪[k]) : k) := by
  have hx' : x ∈ 𝒪[k] := hx.le
  have hm : (⟨x, hx'⟩ : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := by
    rw [mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hx
  rw [q.2.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
  obtain ⟨c, hc⟩ := hm
  have h : x = (c : k) * ((q.1 : 𝒪[k]) : k) := by
    have := congrArg (fun z : 𝒪[k] => (z : k)) hc
    simpa using this.symm
  rw [h, Valuation.map_mul]
  have hc1 : valuation k (c : k) ≤ 1 := c.2
  exact (mul_le_mul_of_nonneg_right hc1 zero_le').trans_eq (one_mul _)

theorem val_unif_lt_one (q : Unif k) : valuation k ((q.1 : 𝒪[k]) : k) < 1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 q.2.not_isUnit

theorem val_unif_pos (q : Unif k) : 0 < valuation k ((q.1 : 𝒪[k]) : k) := by
  rw [zero_lt_iff, Valuation.ne_zero_iff]
  exact fun h => q.2.ne_zero (Subtype.ext h)

variable {D : D7}

theorem val_prF_le_one (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (c : Formalism.L2.Herm.intAf D.host.F D.host.E) : valuation k (p.prF he c.1) ≤ 1 :=
  (p.prF_mem_iff he c.1).2 (mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D p.e PP he).1 c.2)

theorem val_lt_of_mem_idS_of_forall (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}
    (he : Formalism.L2.NTheta.IsIdemAt p.e PP) {I : Ideal (𝓞 D.host.E)} {γ : ValueGroupWithZero k} (hγ : 0 < γ)
    (hI : ∀ a ∈ I, valuation k (p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E a : EAf D)) < γ)
    {s : Formalism.L2.Herm.intAf D.host.F D.host.E} (hs : s ∈ Formalism.L2.DIV.idS D.host.F I) :
    valuation k (p.prF he s.1) < γ := by
  refine Submodule.span_induction (p := fun s _ => valuation k (p.prF he s.1) < γ) ?_ ?_ ?_ ?_ hs
  · rintro _ ⟨a, ha, rfl⟩
    exact hI a ha
  · simpa using hγ
  · intro x y _ _ hx hy
    rw [Subring.coe_add, map_add (f := _)]
    exact Valuation.map_add_lt _ hx hy
  · intro c x _ hx
    rw [smul_eq_mul, Subring.coe_mul, map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (p.val_prF_le_one he c) zero_le').trans_lt (by rwa [one_mul])

theorem val_eq_unif_and_unit : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ t t' : 𝓞 D.host.E, t ∈ PP.asIdeal → t ∉ PP.asIdeal ^ 2 → t' ∉ PP.asIdeal →
    (∃ q : Unif k, valuation k (p.pr (incA D (t : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k)) ∧
      valuation k (p.pr (incA D (t' : D.host.E))) = 1 := by
  intro D k _ _ _ _ p PP he t t' ht ht2 ht'
  let f : 𝓞 D.host.E →+* k :=
    (p.prF he).comp ((Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.comp (Formalism.L2.DIV.oToS D.host.F D.host.E))
  have hf : ∀ x : 𝓞 D.host.E, f x = p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E x : EAf D) := fun _ => rfl
  have hf' : ∀ x : 𝓞 D.host.E, p.pr (incA D (x : D.host.E)) = f x := fun x =>
    (p.prF_toEAf he (incA D (x : D.host.E))).symm
  have hle : ∀ x, valuation k (f x) ≤ 1 := fun x => p.val_prF_le_one he _
  have hlt : ∀ x, x ∈ PP.asIdeal ↔ valuation k (f x) < 1 := fun x => p.mem_iff_val_lt he x
  rw [hf', hf']
  refine ⟨?_, le_antisymm (hle _) (not_lt.1 fun h => ht' ((hlt _).2 h))⟩
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  refine ⟨q, le_antisymm (val_le_unif q ((hlt _).1 ht)) (not_lt.1 fun hlt' => ?_)⟩
  set γ := valuation k ((q.1 : 𝒪[k]) : k) with hγ
  have hγ0 : 0 < γ := val_unif_pos q

  have hPP : Ideal.span {t} ⊔ PP.asIdeal ^ 2 = PP.asIdeal := by
    have h := Ideal.eq_prime_pow_of_succ_lt_of_le (P := PP.asIdeal) (I := Ideal.span {t} ⊔ PP.asIdeal ^ 2) (i := 1)
      PP.ne_bot (lt_of_le_of_ne le_sup_right fun h => ht2 (by
        rw [show (2 : ℕ) = 1 + 1 from rfl, h]
        exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self t)))
      (by
        rw [pow_one]
        exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 ht) (Ideal.pow_le_self two_ne_zero))
    rwa [pow_one] at h
  have hsq : ∀ a ∈ PP.asIdeal ^ 2, valuation k (f a) < γ := by
    intro a ha
    rw [pow_two] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, Valuation.map_mul]
      calc _ ≤ valuation k (f x) * γ := mul_le_mul_of_nonneg_left (val_le_unif q ((hlt _).1 hy)) zero_le'
        _ < 1 * γ := mul_lt_mul_of_pos_right ((hlt _).1 hx) hγ0
        _ = γ := one_mul _
    · rw [map_add (f := _)]; exact Valuation.map_add_lt _ hx hy
  have hall : ∀ a ∈ PP.asIdeal, valuation k (f a) < γ := by
    intro a ha
    rw [← hPP] at ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    rw [map_add (f := _)]
    refine Valuation.map_add_lt _ ?_ (hsq y hy)
    rw [map_mul, Valuation.map_mul]
    exact (mul_le_mul_of_nonneg_right (hle c) zero_le').trans_lt (by rwa [one_mul])

  have hs : toEAf D (p.sec ((q.1 : 𝒪[k]) : k)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart ((p.int_iff _).1 q.1.2)
  let s : Formalism.L2.Herm.intAf D.host.F D.host.E := ⟨_, hs⟩
  have hsv : p.prF he s.1 = ((q.1 : 𝒪[k]) : k) := (p.prF_toEAf he _).trans (p.pr_sec _)
  obtain ⟨a, ha0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot s
  have ha : s - Formalism.L2.DIV.oToS D.host.F D.host.E a ∈ Formalism.L2.DIV.idS D.host.F PP.asIdeal := ha0
  have h2 := val_lt_of_mem_idS_of_forall p he hγ0 hall ha
  have e2 : ((s - Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (s : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, RingHom.map_sub, hsv, ← hf] at h2
  have hγ1 : γ < 1 := val_unif_lt_one q
  have haP : a ∈ PP.asIdeal := (hlt a).2 (by simpa using Valuation.map_sub_lt _ hγ1 (h2.trans hγ1))
  have h3 := Valuation.map_add_lt _ h2 (hall a haP)
  rw [sub_add_cancel] at h3
  exact lt_irrefl _ h3

end GlobalTheory.FinPl.SplitPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_eq_uniformizer_and_unit_at_prime : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∀ t t' : 𝓞 D.host.E, t ∈ PP.asIdeal → t ∉ PP.asIdeal ^ 2 → t' ∉ PP.asIdeal →
    (∃ q : Unif k, valuation k (p.pr (incA D (t : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k)) ∧
      valuation k (p.pr (incA D (t' : D.host.E))) = 1 := by
  first | exact @GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit | exact GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit | (intros; apply GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqLatFrameOfIsSDFrame
section -- merged from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColTOfPinColL
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.LiveModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))

section Emb
open GlobalTheory.MixModel
variable {D : D7}

theorem gram_pos {E : Type} [Field E] [NumberField E] [StarRing E] (hs : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (n : ℕ) :
    (Examples₂.posSpace hs n).gram = 1 := by
  funext i j
  refine (Examples₂.stdSpace_gram_apply hs n (fun _ => false) n 0 i j).trans ?_
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact (if_pos rfl).trans (by simp [Examples₂.sgn])
  · rw [Matrix.one_apply_ne h]; exact if_neg h

theorem rk_top (D : D7) : D.sp.X'.rank + 1 = (D.sp.X D.R.m).rank := by
  have h1 := rankP D
  have h2 := rankN D D.R.m le_rfl
  have h3 : 0 < D.R.N D.R.m := by
    have := D.R.two_le_m
    have h4 : D.R.m * (D.R.t + 1) = D.R.m * D.R.t + D.R.m := by ring
    simp only [Ranks.N]; omega
  omega

def topDec (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1) :
    OrthDec (D.sp.X D.R.m) D.sp.X' (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1) where
  iA := Matrix.of fun b a => if (a : ℕ) = b then 1 else 0
  iB := Matrix.of fun b _ => if D.sp.X'.rank = b then 1 else 0
  isoA := by
    have := rk_top D
    rw [hG, hG', Matrix.mul_one]
    funext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (⟨i, by omega⟩ : Fin (D.sp.X D.R.m).rank)]
    · simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
    · intro b _ hb
      have : ¬ (i : ℕ) = b := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  isoB := by
    have := rk_top D
    rw [hG, Matrix.mul_one]
    funext i j
    have h : (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1).gram i j = 1 := by
      rw [gram_pos, Subsingleton.elim (α := Fin 1) i j, Matrix.one_apply_eq]
    rw [h, Matrix.mul_apply, Finset.sum_eq_single (⟨D.sp.X'.rank, by omega⟩ : Fin (D.sp.X D.R.m).rank)]
    · simp
    · intro b _ hb
      have : ¬ D.sp.X'.rank = b := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  orth := by
    rw [hG, Matrix.mul_one]
    funext i j
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := j.2
    by_cases hb : D.sp.X'.rank = b
    · have : ¬ (j : ℕ) = b := by omega
      simp [this]
    · simp [hb]
  rank_add := rk_top D

theorem iXm_eq (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
    D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b) (b a) : iXm D b a = if (a : ℕ) = b then 1 else 0 := by
  have h0 := rk_top D
  have h1 := rankP D
  have ha := a.2
  have e : ((D.sp.X'.frame.equivFun.trans
      (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)).symm (Pi.single a 1)) =
      D.sp.X'.frame (Fin.cast h1.symm a) := by
    rw [LinearEquiv.symm_apply_eq]
    funext k
    simp [Finsupp.single_apply, Pi.single_apply, Fin.ext_iff, eq_comm]
  rw [iXm, LinearMap.toMatrix'_apply, iXc]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e, hi _ ⟨a, by omega⟩ rfl]
  simp [Finsupp.single_apply, Fin.ext_iff]

theorem isEmbTop_topDec (hG : (D.sp.X D.R.m).gram = 1) (hG' : D.sp.X'.gram = 1)
    (hi : ∀ (a : Fin D.sp.X'.rank) (b : Fin (D.sp.X D.R.m).rank), (a : ℕ) = b →
      D.sp.iX' (D.sp.X'.frame a) = (D.sp.X D.R.m).frame b)
    (c : D.host.E) : IsEmbTop (D := D) (fun j => if j.1 + 1 = D.R.N D.R.m then c else 0)
      ((topDec hG hG').emb.comp (MonoidHom.inl _ _)) := by
  intro h
  have h0 := rk_top D
  have h1 := rankP D
  have h2 := rankN D D.R.m le_rfl
  have eA : (iXm D).map (incA D) = ((topDec hG hG').jA).reindex (finCongr h2) (finCongr h1) := by
    ext b a
    simp [iXm_eq hi, OrthDec.jA, rat, topDec]
  constructor
  · rw [eA]
    have := (topDec hG hG').emb_jA h 1
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M => Matrix.submatrix M _ _) this
  · have := (topDec hG hG').emb_jB h 1
    rw [mt_one, Matrix.mul_one] at this
    funext b
    have e := congrFun (congrFun this (Fin.cast h2.symm b)) (0 : Fin 1)
    have ez : (fun a : Fin (D.R.N D.R.m) => incA D (if a.1 + 1 = D.R.N D.R.m then c else 0)) =
        fun a => (topDec hG hG').jB (Fin.cast h2.symm a) (0 : Fin 1) * incA D c := by
      funext a
      have : (a.1 + 1 = D.R.N D.R.m) ↔ D.sp.X'.rank = a := by omega
      show _ = incA D (if D.sp.X'.rank = a then 1 else 0) * incA D c
      rw [← map_mul]
      by_cases ha : D.sp.X'.rank = a
      · rw [if_pos ha, if_pos (this.2 ha), one_mul]
      · rw [if_neg ha, if_neg (fun h => ha (this.1 h)), zero_mul]
    have ez' := congrFun ez b
    rw [ez, ez', ← e]
    refine Eq.trans ?_ (congrArg (· * incA D c) Matrix.mul_apply).symm
    refine Eq.trans ?_ (Finset.sum_mul _ _ _).symm
    refine Fintype.sum_equiv (finCongr h2.symm) _ _ fun x => ?_
    exact (mul_assoc _ _ _).symm
end Emb


end GlobalTheory.AdForm.LiveModel
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.XGeoStd
open GlobalTheory.AdForm.LiveModel GlobalTheory.AdForm.PinInhab GlobalTheory.MixModel

variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}

abbrev lineZ (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 1

theorem gram_X' {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (hI : I.Ok) : (I.rec7 l Z).sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  have key : ∀ S : HSp (I.rec7 l Z), ∀ n, S = Examples₂.posSpace hs n → S.gram = 1 := by
    rintro _ n rfl; exact gram_pos hs n
  exact key _ _ h2

def oTop {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok) :
    ∀ n, n = (I.rec7 l Z).R.m → OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' (lineZ (I.rec7 l Z)) :=
  fun n h => Eq.rec (motive := fun n _ => OrthDec ((I.rec7 l Z).sp.X n) (I.rec7 l Z).sp.X' (lineZ (I.rec7 l Z)))
    (topDec (gram_X hI _) (gram_X' hI)) h.symm

def piE (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) : (I.rec7 l Z).host.E :=
  ((X.piT u : 𝓞 B.host.E) : B.host.E)

def zeta (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) : Fin (lineZ (I.rec7 l Z)).rank → (I.rec7 l Z).host.E :=
  fun _ => piE I l Z u

def xgeo {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (hI : I.Ok)
    (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (u : B.Word)
    (Λ : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : XGeo (I.rec7 l Z) :=
  ⟨fun _ => stdSp _, vac, lineZ _, oTop l Z hI, zeta I l Z u, 1, Λ⟩

theorem norm_zeta {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    star (zeta I l Z u) ⬝ᵥ (lineZ (I.rec7 l Z)).gram *ᵥ zeta I l Z u = ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) := by
  have h := congrArg (fun z : 𝓞 B.host.E => (z : B.host.E)) (l.pr.piT_norm u)
  rw [gram_pos, Matrix.one_mulVec]
  simp only [dotProduct, zeta, piE, Pi.star_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [map_mul, map_natCast] at h
  rw [show (lineZ (I.rec7 l Z)).rank = 1 from rfl, one_smul]
  exact (mul_comm _ _).trans h

theorem isLineVec_zeta {I : TC B X} (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    IsLineVec (lineZ (I.rec7 l Z)) (zeta I l Z u) := by
  refine ⟨rfl, ?_⟩
  rw [norm_zeta]
  have := (l.pr.T_prime u).ne_zero
  exact_mod_cast this

theorem eq_latFrame_of_isSDFrame {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (h : IsSDFrame V β Λ 1) : Λ = GlobalTheory.PlaceModel.latFrame V := by
  obtain ⟨c, -, -, -, h4, h5⟩ := h
  ext x
  constructor
  · intro hx
    have := h5 x hx
    rw [one_pow, Nat.cast_one, one_smul] at this
    rw [← SetLike.mem_coe, GlobalTheory.PlaceModel.coe_latFrame]
    exact this
  · intro hx
    rw [← SetLike.mem_coe, GlobalTheory.PlaceModel.coe_latFrame] at hx
    have := h4 x hx
    rwa [one_pow, Nat.cast_one, one_smul] at this

end GlobalTheory.XGeoStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemOfCoprime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.PkOf

section Heq

open _root_.Formalism.L2 _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef

variable {D : D7}

theorem mu_of_heq {Bs : DefBase D.what₂.LL} {Df Df' : DefSide Bs} (h : Df = Df') {S0 : IndefData Df} {S1 : IndefData Df'}
    (hS : HEq S0 S1) : S0.μ = S1.μ := by
  subst h
  cases eq_of_heq hS
  rfl

end Heq

theorem natCast_not_mem_of_coprime {E : Type} [Field E] [NumberField E] (PP : HeightOneSpectrum (𝓞 E)) {n p : ℕ}
    (hc : Nat.Coprime n p) (hp : (p : 𝓞 E) ∈ PP.asIdeal) : (n : 𝓞 E) ∉ PP.asIdeal := by
  intro hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 E))
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hp)

theorem exists_of_mem_QE {X : Formalism.L2.Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {ξ : Formalism.L2.DIV.Chr X.F X.E X.K} {PP : HeightOneSpectrum (𝓞 X.E)} (h : PP ∈ Formalism.L2.Col.QE sel ξ) : ∃ v, PP = sel v := by
  classical
  unfold Formalism.L2.Col.QE at h
  split_ifs at h with hf
  · obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 h
    exact ⟨v, rfl⟩
  · simp at h

end GlobalTheory.Fam.PkOf

namespace GlobalTheory.Fam

end GlobalTheory.Fam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairFrameCoordinatesIntegralAndFunctiona
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairFrameCoordinatesIntegralAndFunctiona
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.StdPairCoord

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_lat_iff {D : D7} {p : SplitPt D k} {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank)
    (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)} (h : β.IsLat L Λ) (x : Fin S.rank → k) :
    x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := by
  rw [h x, GlobalTheory.SeeSaw.StdOff.mem_latV_int hL]
  exact forall_congr' fun r =>
    ((p.int_iff _).trans (and_iff_right (GlobalTheory.SeeSaw.StdOff.sec_mem_idAt p _)).symm).symm

theorem hasVal_mulVec {n : ℕ} (Q : Pair k (Fin n)) (b' : Matrix (Fin n) (Fin n) k) (s : Fin n → 𝒪[k])
    (h : ∀ r, Q.HasVal (b' *ᵥ Pi.single r 1) (residue 𝒪[k] (s r))) (y : Fin n → 𝒪[k]) :
    Q.HasVal (b' *ᵥ fun r => (y r : k)) (∑ r, residue 𝒪[k] (y r) * residue 𝒪[k] (s r)) := by
  have h1 : ∀ t : Finset (Fin n), Q.HasVal (∑ r ∈ t, y r • (b' *ᵥ Pi.single r 1))
      (∑ r ∈ t, residue 𝒪[k] (y r) * residue 𝒪[k] (s r)) := fun t => by
    induction t using Finset.induction_on with
    | empty => exact ⟨by simp, by simp only [Finset.sum_empty]; exact map_zero Q.fn⟩
    | insert r t hr ih =>
      rw [Finset.sum_insert hr, Finset.sum_insert hr]
      exact ((h r).smul _).add ih
  convert h1 Finset.univ using 1
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]
  rfl

end GlobalTheory.AdForm.StdPairCoord


open GlobalTheory.AdForm.StdPairCoord in
theorem GlobalTheory.AdForm.stdT_pair_coords : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ i (r₀ : Fin ((I.rec7 l Z).sp.X j).rank), r₀.1 + 1 = ((I.rec7 l Z).sp.X j).rank → ∀ (x : Fin ((I.rec7 l Z).sp.X j).rank → k) (a : 𝓀[k]), (Q j i).HasVal x a ↔ ∃ y : Fin ((I.rec7 l Z).sp.X j).rank → 𝒪[k], (∀ r, (y r : k) = ((β j i).b *ᵥ x) r) ∧ ∃ s : 𝒪[k], (s : k) = (p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E))) ∧ a = residue 𝒪[k] (s * y r₀) := by
  intro B X I l Z u k _ _ _ _ ι p β Q L hS j hj i r₀ hr₀ x a
  obtain ⟨-, hT⟩ := hS
  obtain ⟨hL, hT'⟩ := hT j hj
  obtain ⟨hlat, hfn⟩ := hT' i
  have hmem := mem_lat_iff hL (β j i) hlat
  have hs : ∀ r, ∃ s : 𝒪[k], (s : k) = (if r = r₀ then (p i).pr (incA (I.rec7 l Z)
      (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E))) else 0) ∧
      (Q j i).HasVal ((β j i).b' *ᵥ Pi.single r 1) (residue 𝒪[k] s) := fun r => by
    have hz : (Pi.single r 1 : Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E) ∈ L j := (hL _).2 fun t => by
      rw [Pi.single_apply]
      split_ifs
      exacts [isIntegral_one, isIntegral_zero]
    obtain ⟨s, hs1, hs2⟩ := hfn _ hz r₀ hr₀
    have e : (fun r' => (p i).pr (incA (I.rec7 l Z) ((Pi.single r 1 : Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E) r'))) =
        Pi.single r 1 := funext fun r' => by
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs
      · rw [map_one, map_one]
      · rw [map_zero, map_zero]
    rw [e] at hs2
    refine ⟨s, ?_, hs2⟩
    rw [hs1, Pi.single_apply]
    by_cases h : r₀ = r
    · subst h
      rw [if_pos rfl, if_pos rfl, mul_one]
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero, map_zero, map_zero]
  choose s hs using hs
  have key : ∀ y : Fin ((I.rec7 l Z).sp.X j).rank → 𝒪[k], (Q j i).HasVal ((β j i).b' *ᵥ fun r => (y r : k))
      (residue 𝒪[k] (s r₀ * y r₀)) := fun y => by
    have h1 := hasVal_mulVec (Q j i) (β j i).b' s (fun r => (hs r).2) y
    convert h1 using 1
    rw [Finset.sum_eq_single r₀ (fun r _ hr => ?_) (fun h => (h (Finset.mem_univ _)).elim), map_mul, mul_comm]
    have : s r = 0 := Subtype.ext ((hs r).1.trans (if_neg hr))
    rw [this, map_zero, mul_zero]
  constructor
  · intro h
    have hx := (hmem x).1 h.mem
    refine ⟨fun r => ⟨_, hx r⟩, fun r => rfl, s r₀, (hs r₀).1.trans (if_pos rfl), h.unique ?_⟩
    have := key fun r => ⟨_, hx r⟩
    rwa [show ((β j i).b' *ᵥ fun r => (((⟨_, hx r⟩ : 𝒪[k]) : k))) = x by
      rw [show (fun r => (((⟨_, hx r⟩ : 𝒪[k]) : k))) = (β j i).b *ᵥ x from rfl, Matrix.mulVec_mulVec, (β j i).b'b,
        Matrix.one_mulVec]] at this
  · rintro ⟨y, hy, s', hs', rfl⟩
    obtain rfl : s' = s r₀ := Subtype.ext (hs'.trans ((hs r₀).1.trans (if_pos rfl)).symm)
    have hx : x = (β j i).b' *ᵥ fun r => (y r : k) := by
      rw [show (fun r => (y r : k)) = (β j i).b *ᵥ x from funext hy, Matrix.mulVec_mulVec, (β j i).b'b, Matrix.one_mulVec]
    rw [hx]
    exact key y

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairFrameCoordinatesIntegralAndFunctionaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPair_frameCoordinates_integral_and_functional : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank)) (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)), GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ j, j ≤ B.R.m → ∀ i (r₀ : Fin ((I.rec7 l Z).sp.X j).rank), r₀.1 + 1 = ((I.rec7 l Z).sp.X j).rank → ∀ (x : Fin ((I.rec7 l Z).sp.X j).rank → k) (a : 𝓀[k]), (Q j i).HasVal x a ↔ ∃ y : Fin ((I.rec7 l Z).sp.X j).rank → 𝒪[k], (∀ r, (y r : k) = ((β j i).b *ᵥ x) r) ∧ ∃ s : 𝒪[k], (s : k) = (p i).pr (incA (I.rec7 l Z) (show (I.rec7 l Z).host.E from (B.fields.conjO (X.piT u) : B.fields.E))) ∧ a = residue 𝒪[k] (s * y r₀) := by
  first | exact @GlobalTheory.AdForm.stdT_pair_coords | exact GlobalTheory.AdForm.stdT_pair_coords | (intros; apply GlobalTheory.AdForm.stdT_pair_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeRationalLineTraceFractionalIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeRationalLineTraceFractionalIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatLine

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.IdVMul

variable {D : D7}

theorem mul_idV_int {𝔠 : FI D} {v : GlobalTheory.FinPl.Pl D} {a : AE D}
    (h : ∀ c ∈ 𝔠, incA D c * a ∈ intAt D (· = v)) {y : AE D} (hy : y ∈ idV 𝔠 v) : y * a ∈ intAt D (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, c, hc, rfl⟩ := hy
    have e := incA_mul_tmul (D := D) c (pairA D.host.F 0 α) 1
    rw [mul_one] at e
    rw [← e, mul_comm (incA D c), mul_assoc]
    exact intAt_mul (tmul_one_mem_intAt hα h0) (h c hc)
  | zero => rw [zero_mul]; exact intAt_zero
  | add x y _ _ hx hy => rw [add_mul]; exact intAt_add hx hy
  | neg x _ hx => rw [neg_mul]; exact intAt_neg hx

theorem mem_idV_inv {𝔠 : FI D} (h𝔠 : 𝔠 ≠ 0) {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ idAt D (· = v))
    (h : ∀ c ∈ 𝔠, incA D c * a ∈ intAt D (· = v)) : a ∈ idV 𝔠⁻¹ v := by
  obtain ⟨b, hb0, hb⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠⁻¹ (inv_ne_zero h𝔠)
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.IdVGen.idV_gen D v 𝔠 h𝔠
  have hm := idV_mul_gen D v 𝔠⁻¹ 𝔠 b c hb0 hc0 hb hc (GlobalTheory.FinPlLoc.idem D (· = v))
  rw [inv_mul_cancel₀ h𝔠, GlobalTheory.SeeSaw.idV_one_eq_intAt] at hm
  obtain ⟨h1, h2⟩ := hm.1 (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  have h3 : incA D b⁻¹ * GlobalTheory.FinPlLoc.idem D (· = v) ∈ idV 𝔠 v := by
    refine (hc _).2 ⟨?_, Ideal.mul_mem_left _ _ h2⟩
    rw [← mul_assoc, ← map_mul, ← mul_inv, mul_comm c b]
    exact h1
  have h4 := mul_idV_int h h3
  rw [mul_assoc, (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha] at h4
  exact (hb a).2 ⟨h4, ha⟩

theorem pairing_smul_ratV (S : HSp D) (s x : Fin S.rank → D.host.E) (a : AE D) :
    pairing S s (a • ratV x) = incA D (∑ b, row S s b * x b) * a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pairing, ratV, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem incA_inj : Function.Injective (incA D) := GlobalTheory.MixModel.incA_injective

theorem smul_mem_latV {S : HSp D} {L : Lat S} {x : Fin S.rank → D.host.E} {𝔞 : FI D} (h : ∀ t ∈ 𝔞, t • x ∈ L)
    {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ idV 𝔞 v) : a • ratV x ∈ latV S L (· = v) := by
  induction ha using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, h0, t, ht, rfl⟩ := hy
    have e := incA_mul_tmul (D := D) t (pairA D.host.F 0 α) 1
    rw [mul_one] at e
    have := int_mul_mem (tmul_one_mem_intAt hα h0) (h t ht)
    convert this using 1
    funext i
    rw [← e]
    simp only [ratV, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  | zero => rw [zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_smul]; exact neg_mem hx

theorem line_trace : ∀ (D : D7) (S : HSp D) (L : Lat S) (x : Fin S.rank → D.host.E), IsSelfDualC S L → x ≠ 0 → ∃ 𝔞 : FI D, 𝔞 ≠ 0 ∧ (∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔞) ∧ ∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ idAt D (· = v), a • ratV x ∈ latV S L (· = v) ↔ a ∈ idV 𝔞 v := by
  intro D S L x hL hx
  obtain ⟨m, s, s', hs, hs', hexp⟩ := exists_expansion hL
  set c : Fin m → D.host.E := fun l => ∑ b, row S (s' l) b * x b with hc
  have hx' : ∀ i, x i = ∑ l, c l * s l i := by
    intro i
    apply incA_inj (D := D)
    have := hexp ((1 : AE D) • ratV x) i
    simp only [pairing_smul_ratV, mul_one] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simpa only [one_smul, ratV, map_mul] using this
  set 𝔠 : FI D := FractionalIdeal.spanFinset (𝓞 D.host.E) Finset.univ c with h𝔠def
  have hmem : ∀ y, y ∈ 𝔠 ↔ y ∈ Submodule.span (𝓞 D.host.E) (Set.range c) := by
    intro y
    rw [← FractionalIdeal.mem_coe, h𝔠def, FractionalIdeal.spanFinset_coe, Finset.coe_univ, Set.image_univ]
  have h𝔠 : 𝔠 ≠ 0 := by
    intro h0
    apply hx
    funext i
    rw [hx' i]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : c l ∈ 𝔠 := (hmem _).2 (Submodule.subset_span ⟨l, rfl⟩)
    rw [h0, FractionalIdeal.mem_zero_iff] at this
    rw [this, zero_mul]
  have hglob : ∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔠⁻¹ := by
    intro t
    rw [FractionalIdeal.mem_inv_iff h𝔠]
    constructor
    · intro ht y hy
      rw [hmem] at hy
      rw [← FractionalIdeal.mem_coe]
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, rfl⟩ := hy
        obtain ⟨o, ho⟩ := (hL.2 _).1 ht (s' l) (hs' l)
        rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
        refine ⟨o, ho.trans ?_⟩
        rw [Finset.sum_comm]
        simp only [hc, GlobalTheory.FinPl.FrameLat.row, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      | zero => rw [mul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | smul o y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
    · intro ht
      have ho : ∀ l, ∃ o : 𝓞 D.host.E, algebraMap _ D.host.E o = t * c l := fun l =>
        (FractionalIdeal.mem_one_iff _).1 (ht _ ((hmem _).2 (Submodule.subset_span ⟨l, rfl⟩)))
      choose o ho using ho
      have : t • x = ∑ l, o l • s l := by
        funext i
        rw [Pi.smul_apply, smul_eq_mul, hx' i, Finset.mul_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Pi.smul_apply, Algebra.smul_def, ho, mul_assoc]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => L.smul_mem _ (hs l)
  refine ⟨𝔠⁻¹, inv_ne_zero h𝔠, hglob, fun v a ha => ⟨fun h => ?_, smul_mem_latV fun t ht => (hglob t).2 ht⟩⟩
  refine mem_idV_inv h𝔠 ha fun y hy => ?_
  rw [hmem] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    refine ⟨Ideal.mul_mem_left _ _ ha, ?_⟩
    have := pairing_int hL (hs' l) h
    rwa [pairing_smul_ratV] at this
  | zero => rw [map_zero, zero_mul]; exact intAt_zero
  | add y z _ _ hy hz => rw [map_add (f := _), add_mul]; exact intAt_add hy hz
  | smul o y hy' hy =>
    have h1 := GlobalTheory.IdVGen.gen_mem_intAt (v := v) (GlobalTheory.FinPlLoc.ePl_int (· = v))
      (fun w hw => by rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw]) o
    have e := incA_mul_tmul (D := D) (algebraMap (𝓞 D.host.E) D.host.E o) (pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v))) 1
    rw [mul_one] at e
    have h2 := intAt_mul h1 hy
    rw [← e] at h2
    have h3 : GlobalTheory.FinPlLoc.idem D (· = v) * a = a := (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha
    convert h2 using 1
    rw [Algebra.smul_def, map_mul]
    conv_lhs => rw [← h3]
    simp only [GlobalTheory.FinPlLoc.idem]
    ring

end GlobalTheory.Core.Mi.LatLine

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeRationalLineTraceFractionalIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_rationalLineTrace_fractionalIdeal : ∀ (D : D7) (S : HSp D) (L : Lat S) (x : Fin S.rank → D.host.E), IsSelfDualC S L → x ≠ 0 → ∃ 𝔞 : FI D, 𝔞 ≠ 0 ∧ (∀ t : D.host.E, t • x ∈ L ↔ t ∈ 𝔞) ∧ ∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ idAt D (· = v), a • ratV x ∈ latV S L (· = v) ↔ a ∈ idV 𝔞 v := by
  first | exact @GlobalTheory.Core.Mi.LatLine.line_trace | exact GlobalTheory.Core.Mi.LatLine.line_trace | (intros; apply GlobalTheory.Core.Mi.LatLine.line_trace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardDatumSplitPlacesOverLevelPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardDatumSplitPlacesOverLevelPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

namespace GlobalTheory.AdForm

theorem stdT_levelPrime_mem_v : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ i, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal := by
  intro B X I _ _ l Z u k _ _ _ _ ι p β Q L hS i
  obtain ⟨e, he⟩ := hS.1
  have hv := GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under (p i) (he i)
  have hT := GlobalTheory.ColNorms.BadPrimes.T_mem (GlobalTheory.BasePrimes.primes_ok B X).1 (e i).2
  rw [hv]
  show _ ∈ Ideal.under _ _
  rw [Ideal.mem_under, map_natCast]
  exact hT

end GlobalTheory.AdForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardDatumSplitPlacesOverLevelPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardDatum_splitPlaces_over_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    GlobalTheory.AdForm.StdT I l Z u p β Q L → ∀ i, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal := by
  first | exact @GlobalTheory.AdForm.stdT_levelPrime_mem_v | exact GlobalTheory.AdForm.stdT_levelPrime_mem_v | (intros; apply GlobalTheory.AdForm.stdT_levelPrime_mem_v <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatEqOfCarries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BaseCosetPt

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem lat_eq_of_carries {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N₁ N₂ : Submodule (𝓞 E) (Fin n → E)}
    (h₁ : Submodule.IsFullLattice E N₁) (h₂ : Submodule.IsFullLattice E N₂)
    (c₁ : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N₁) (c₂ : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N₂) :
    N₁ = N₂ := by
  have key : ∀ N : Submodule (𝓞 E) (Fin n → E), Submodule.IsFullLattice E N → ∀ x : Fin n → E,
      (x ∈ N ↔ (fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) ∈ Formalism.L2.Herm.hatL (F := F) N) := by
    intro N hN x
    let : Submodule.IsFullLattice E N := hN
    have hone := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.mpr hN.fg) (Submodule.IsFullLattice.span_eq_top (A := E) (M := N))
    conv_lhs => rw [← hone]
    show (((1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) N ↔ _
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  ext x
  rw [key N₁ h₁, key N₂ h₂, c₁, c₂]

end Gen

section Pt

open _root_.Formalism.L2.Col Formalism.MainNotions _root_.Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem frsF_symm_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) {w : Sp X.E (R.N j)}
    (hw : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N) : (frsF sel mu p P).symm w ∈ stdAt X.E (R.N j) P.1 := by
  have hfr := isFr_ptFr p P.1
  rw [← frsF_eq_ptFr sel mu p P] at hfr
  exact (hfr _).1 (by simpa using hw)

theorem frsF_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) {x : Sp X.E (R.N j)}
    (hx : x ∈ stdAt X.E (R.N j) P.1) : frsF sel mu p P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N := by
  have hfr := isFr_ptFr p P.1
  rw [← frsF_eq_ptFr sel mu p P] at hfr
  exact (hfr _).2 hx

theorem cosetIn_eq_of {u : Pr.Word} {j : ℕ} (r : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : Sp X.E (R.N j)) (e : rowSG Pr sel mu → ℤ) (he : e P = 0)
    (hY : r.1.2 = {z | z - y ∈ locLat (rowSG Pr sel mu) r.1.1.deco.1.N e}) :
    cosetIn r P = {z | z - (frsF sel mu r.1.1 P).symm y ∈ stdAt X.E (R.N j) P.1} := by
  classical
  apply Set.ext
  intro z
  simp only [cosetIn, if_pos hP, pow_zero, inv_one, one_smul, Set.mem_setOf_eq, hY]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : y' - y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal r.1.1.deco.1.N := by
      have := (Submodule.mem_iInf _).1 hy' P
      simpa [Submodule.mem_comap, he] using this
    have := add_mem hz (frsF_symm_mem r.1.1 P h1)
    rwa [map_sub, sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, by simp, hz⟩

end Pt

end GlobalTheory.BaseCosetPt

namespace GlobalTheory.BaseCosetPt

open _root_.Formalism.L2.Col Formalism.MainNotions _root_.Formalism.L2.DIV

end GlobalTheory.BaseCosetPt
end
end
