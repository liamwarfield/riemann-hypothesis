module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartLevelStandardBasePointEqMember
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBad
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LvSameZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRepresentativeDiffersByLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRepresentativeDiffersByLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.RepZero

open _root_.Formalism.L2.Col GlobalTheory.Mem.Col2.StepZero

theorem chr_of_down_eq_one {X : Fields} {n : ℕ} {ST SG Q : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers X.E))}
    {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
    (pref : DecoF X.E n ST SG Q → Prop) {Λ₀ : LevFam X.E X.K n SG} (hΛ : ∀ b, Λ b = Λ₀) (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q)
    (b : β) (g : (stepY ST y β Λ Θ pref).G b) (h : down pref hΛ b g = 1) : (stepY ST y β Λ Θ pref).chr b g = 1 := by
  show (Λ b).chr g.2.1 * (Θ b).chr g.2.2 = 1
  rw [chr_eq_one (hΘ b), mul_one, chr_congr (hΛ b)]
  have e : (⟨g.2.1.1, hΛ b ▸ g.2.1.2⟩ : Λ₀.grp) = (down pref hΛ b g).2 := rfl
  rw [e, h]
  exact map_one _

theorem exists_lift_one {X : Fields} {n : ℕ} {ST SG Q : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers X.E))}
    {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q}
    (pref : DecoF X.E n ST SG Q → Prop) {Λ₀ : LevFam X.E X.K n SG} (hy : ∀ N, y.ys N = {∅}) (hΛ : ∀ b, Λ b = Λ₀)
    (hΘ : ∀ b, Θ b = LevQFam.top X.E X.K n Q) (b : β) (p q : (stepY ST y β Λ Θ pref).D b) (h : p.1.1.deco = q.1.1.deco) :
    ∃ g : (stepY ST y β Λ Θ pref).G b, (stepY ST y β Λ Θ pref).gam b g = 1 ∧ g • p = q ∧ (stepY ST y β Λ Θ pref).chr b g = 1 := by
  obtain ⟨g, h2, h3⟩ := exists_lift pref hy hΛ hΘ b p q 1 (by rw [one_smul]; exact h)
  exact ⟨g, (congrArg (fun g => ufGL X.E n g.1) h2).trans (map_one _), h3, chr_of_down_eq_one pref hΛ hΘ b g h2⟩

end GlobalTheory.Fam.RepZero


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Fam.rep_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ c : {c // A.chOf 0 c = β}, ∃ κ : (A.K 0 (Nat.zero_le _) β).lev.U, ((C.forms u).to0.cls0.y ((I.eCls0 l u a).symm c.1)).1 = ((A.K 0 (Nat.zero_le _) β).y c).1 * κ.1 ∧ (A.K 0 (Nat.zero_le _) β).lev.chi κ = 1 := by
  set_option maxHeartbeats 4000000 in
    intro B X I hI _ l Z C hC u a Ch A hA β hk c
    obtain ⟨c, rfl⟩ := c
    set c' := (I.eCls0 l u a).symm c with hc'
    have hR := hA.reads 0 (Nat.zero_le _)
    have hyS : ((C.forms u).to0.cls0.y c').1 = I.yStd u 0 c' := (hC u).yE 0 (Nat.zero_le _) (Or.inl rfl) c'
    have hS := MemChart.yStd_spec I hI u 0 c'
    set yc : TC.GA B (B.R.N 0) := ((A.K 0 (Nat.zero_le _) (A.chOf 0 c)).y ⟨c, rfl⟩).1 with hyc
    have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
    let q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0 := extTo (I.Q a) (extTo I.SQ ((I.stp u I.mu0 0).rep c').1.1)
    have hq : TC.PtOf (yc * (yc⁻¹ * I.yStd u 0 c') * A.kb 0 (A.chOf 0 c)) q := by
      rw [mul_inv_cancel_left, hk]
      exact IsPtOf.extTo (I.Q_subset_SQ a) hd hS
    have hL := hI.idx_ok a
    have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
    have hΛ := StepZero.levGAt_zero (I.Tp a) hL
    have hΘ := StepZero.levQAt_zero (I.Tp a) hL
    have e : ((I.stp u a 0).rep c).1.1.deco = ((I.stp u I.mu0 0).rep c').1.1.deco := by
      have := TC.StepZero.rep_eCls0 I hI l u a c'
      rwa [hc', Equiv.apply_symm_apply] at this
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, hgam, h3, hchr⟩ := RepZero.exists_lift_one ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p
      (by rw [hp]; exact e)
    have hact : ((I.stp u a 0).act c.1 g ((I.stp u a 0).rep c)).1.1 = q :=
      (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
    have hmem : yc⁻¹ * I.yStd u 0 c' ∈ (A.K 0 (Nat.zero_le _) (A.chOf 0 c)).lev.U :=
      (hR.lev c _ q hq).2 ⟨g, hgam, hact, TC.Chart0.cos0 I _ _⟩
    refine ⟨⟨yc⁻¹ * I.yStd u 0 c', hmem⟩, ?_, ?_⟩
    · show _ = yc * (yc⁻¹ * I.yStd u 0 c')
      rw [hyS, mul_inv_cancel_left]
    · have hpt2 : TC.PtOf (yc * (yc⁻¹ * I.yStd u 0 c') * A.kb 0 (A.chOf 0 c))
          ((I.stp u a 0).act c.1 g ((I.stp u a 0).rep c)).1.1 := by
        rw [hact]
        exact hq
      have hc := hR.chr c ⟨yc⁻¹ * I.yStd u 0 c', hmem⟩ g hgam hpt2
      apply Units.ext
      refine hc.trans ?_
      rw [hchr]
      simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRepresentativeDiffersByLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_representative_differs_by_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ c : {c // A.chOf 0 c = β}, ∃ κ : (A.K 0 (Nat.zero_le _) β).lev.U, ((C.forms u).to0.cls0.y ((I.eCls0 l u a).symm c.1)).1 = ((A.K 0 (Nat.zero_le _) β).y c).1 * κ.1 ∧ (A.K 0 (Nat.zero_le _) β).lev.chi κ = 1 := by
  first | exact @GlobalTheory.Fam.rep_zero_std | exact GlobalTheory.Fam.rep_zero_std | (intros; apply GlobalTheory.Fam.rep_zero_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartCharacterEqMemberChartCharacterStdB
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartCharacterEqMemberChartCharacterStdB
noncomputable section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.ChiZero

open GlobalTheory.Mem.Col2.MemChart

theorem redAt_eq_one_of_congAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n D : ℕ} (hD : 1 ≤ D)
    (P : Pl E) (w : St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) (h : GlobalTheory.TwU.CongAt P D w.1) : redAt 1 P w = 1 := by
  obtain ⟨_, y, rfl⟩ := w
  have e : redAt 1 P ⟨frGL 1 y, ⟨y, rfl⟩⟩ = bc (resS F P) y := by
    show bc (resS F P) (pullFr 1 ⟨frGL 1 y, ⟨y, rfl⟩⟩) = _
    rw [pullFr_frGL]
  rw [e]
  have e1 : frGL 1 y = intGL F E n y := by simp [frGL]
  apply Units.ext
  ext a b
  obtain ⟨s, hs, hm⟩ := h a b
  have hq : ((Formalism.L2.Col.qOf P : ℕ) : E) ≠ 0 := by
    have : Formalism.L2.Col.qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  have hqm : Ideal.Quotient.mk P.asIdeal ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.absNorm_mem _)
  have key : oToS F E s * ((y.1 - 1) a b) = oToS F E ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 E) ^ D * ⟨_, hm⟩ := by
    apply Subtype.ext
    have c1 : ∀ r : 𝓞 E, ((oToS F E r : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = iA F E (algebraMap (𝓞 E) E r) := fun _ => rfl
    have c2 : (((y.1 - 1) a b : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = ((frGL 1 y).1 - 1) a b := by
      rw [e1, Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    rw [Subring.coe_mul, Subring.coe_mul, SubmonoidClass.coe_pow, c1, c1, c2, ← map_pow, map_natCast]
    show _ = _ * (_ * (_ * _))
    rw [mul_left_comm, ← mul_assoc (iA F E (_ ^ D)), ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one, one_mul]
  have k2 := congrArg (resS F P) key
  rw [map_mul, map_mul, map_pow, resS_oToS, resS_oToS, hqm, zero_pow (by omega), zero_mul] at k2
  haveI := P.isPrime
  have k3 := (mul_eq_zero.1 k2).resolve_left (fun h0 => hs (Ideal.Quotient.eq_zero_iff_mem.1 h0))
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at k3
  show resS F P (y.1 a b) = (1 : Matrix (Fin n) (Fin n) (kP P)) a b
  rw [k3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem dia_of_base (hPr : (B.primes X).Ok) (u : B.Word) {n : ℕ} [NeZero n] {Q : Finset (HeightOneSpectrum (𝓞 B.fields.E))} {g k : GA B n}
    (k1 : ∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n)
    (k2 : ∀ w ∈ (B.primes X).vGs, bc (prV (E := B.host.E) (w.under (𝓞 B.host.F))) k = 1)
    (k3 : ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j))
      (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0))
    {p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs Q} (h : PtOf (g * k) p) :
    g ∈ UAd B.sp.cm n ∧ (decoOf ((B.primes X).vT u) (B.primes X).vGs g).dia (diaT (Pr := B.primes X) u) = p.deco := by
  refine GlobalTheory.T.decoratedLattice_diagonalBasePoint_mul _ _ B.sp.cm n _ _ Q g _ p _ h k1 k2 fun P r j hr => ?_
  have hu : IsUnit (Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u))) := by
    have h0 : Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO ((B.primes X).piT u)) ≠ 0 := fun h0 =>
      (basePi_of_ok (GlobalTheory.Mem.FieldsLaws.fields_ok B) hPr u).conj_notMem P.2 (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    exact @Ne.isUnit (Res P.1) _ _ h0
  have e : ((diaT (Pr := B.primes X) u P : (𝓞 B.fields.E ⧸ P.1.asIdeal)ˣ) : 𝓞 B.fields.E ⧸ P.1.asIdeal) =
      Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) := by
    unfold diaT
    rw [dite_eq_left hu]
    rfl
  rw [e]
  exact k3 P r j hr

abbrev levelZeroSubgroupOfWord (u : B.Word) : Subgroup (GA B (B.R.N 0)) :=
  levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp

abbrev typ0 (u : B.Word) : levelZeroSubgroupOfWord I u →* ℂˣ :=
  levTyp (F := B.host.F) (hc := B.sp.cm) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr)


set_option maxHeartbeats 1000000 in
theorem stepZeroChartLevel_mem_columnLevel_of_stdBase (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a 0).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N 0) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N 0))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a 0).Cl → GA B (B.R.N 0)} {st : ∀ c, (I.stp u a 0).Stab c → GL (Fin (B.R.N 0)) B.host.E}
    {k : Ch → GA B (B.R.N 0)} (hR : I.Reads u a 0 chOf Lb U chi y st k) (c : (I.stp u a 0).Cl)
    (k2 : ∀ w ∈ (B.primes X).vGs, bc (prV (E := B.host.E) (w.under (𝓞 B.host.F))) (k (chOf c)) = 1)
    (x : U (chOf c)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (hq : PtOf (y c * x.1 * k (chOf c)) q) :
    ∃ hx : x.1 ∈ levelZeroSubgroupOfWord I u, chi (chOf c) x = typ0 I u ⟨x.1, hx⟩ := by
  have hL := hI.idx_ok a
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  obtain ⟨κ, h1, h2, -⟩ := (hR.lev c x.1 q hq).1 x.2
  subst h2
  have hg := dia_of_base hPr u (hR.k_std _) k2 (hR.k_T _) (hR.pt c)
  have hx := dia_of_base hPr u (hR.k_std _) k2 (hR.k_T _) hq
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • _ = _
    rw [e1]
    rfl)
  have hm : κ.2.1.1 ∈ (colLev I.Ch 0).grp := hΛ c.1 ▸ κ.2.1.2
  have hxU : x.1 ∈ levelZeroSubgroupOfWord I u := (mem_levU _ _ _ _ _).2 ⟨hJ, by rw [hr]; exact inv_mem hm⟩
  refine ⟨hxU, Units.ext ((hR.chr c x κ h1 hq).trans (Eq.symm ?_))⟩
  have e2 : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x.1, hxU⟩ = (⟨κ.2.1.1, hm⟩ : (colLev I.Ch 0).grp)⁻¹ :=
    Subtype.ext hr
  show ((Units.map B.embLL.toMonoidHom ((colLev I.Ch 0).chr (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x.1, hxU⟩)))⁻¹ : ℂˣ).1 =
    B.embLL (((Chart0.lvG I a c.1).chr κ.2.1 * (Chart0.lvQ I a c.1).chr κ.2.2 : B.LLˣ) : B.LL)
  rw [e2, StepZero.chr_eq_one (hΘ c.1), mul_one, StepZero.chr_congr (hΛ c.1), map_inv, map_inv, inv_inv]
  rfl

theorem stepZeroColumnLevelType_eq_of_congruent_typePrimes (u : B.Word) (x x' : levelZeroSubgroupOfWord I u)
    (h : ∀ w ∈ (B.primes X).vGs, ∃ D, 1 ≤ D ∧ GlobalTheory.TwU.CongAt (F := B.host.F) (E := B.host.E) w D (x.1⁻¹ * x'.1)) :
    typ0 I u x = typ0 I u x' := by
  have e : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ (x⁻¹ * x') = 1 := by
    apply Subtype.ext
    funext w
    obtain ⟨D, hD, hc⟩ := h w.1 w.2
    exact redAt_eq_one_of_congAt hD w.1 ⟨(x⁻¹ * x').1, congruence_subgroup_le_stabilizer _ _ _ (unipotentLevel_le_mirabolicLevel _ _ _ _ _ (x⁻¹ * x').2)⟩ hc
  have e2 : typ0 I u (x⁻¹ * x') = 1 := by
    show (((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr) (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ (x⁻¹ * x')))⁻¹ = 1
    rw [e, map_one, inv_one]
  rw [map_mul, map_inv, inv_mul_eq_one] at e2
  exact e2

end GlobalTheory.Fam.ChiZero
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam
open GlobalTheory.Fam.ChiZero GlobalTheory.Mem.Col2.MemChart


set_option maxHeartbeats 4000000 in
theorem chi_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (x : (A.K 0 (Nat.zero_le _) β).lev.U) (x' : (C.forms u).to0.cls0.lev.U), x.1 = x'.1 → (A.K 0 (Nat.zero_le _) β).lev.chi x = (C.forms u).to0.cls0.lev.chi x' := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ x x' hxx
  have hPr := l.pr
  haveI : NeZero (B.R.N 0) := ⟨(B.R.N_pos 0).ne'⟩
  obtain ⟨c, rfl⟩ := hA.chOf_onto 0 (Nat.zero_le _) β
  have hR := hA.reads 0 (Nat.zero_le _)
  obtain ⟨n, hn, hfin⟩ := hA.fin 0 (Nat.zero_le _) (A.chOf 0 c)
  obtain ⟨x₁, e₁, ⟨q, hq⟩, hcg⟩ := GlobalTheory.Mem.Col2.AdT.LevelElt.exists_level_elt I hI hP l Z u a 0 (Nat.zero_le _) (A.bad 0) (Ch 0) (A.chOf 0)
    (A.K 0 (Nat.zero_le _)) (A.kb 0) hR c ⟨n, hn, fun κ _ => hfin κ⟩ x
  obtain ⟨hx₁, f₁⟩ := stepZeroChartLevel_mem_columnLevel_of_stdBase I hI hPr u a hR c (fun w hw => by
    rw [hβ]
    exact (kStd_spec hPr u _).2.1 _ fun hT => Formalism.L2.Col.rls_T_notUnder hPr u _ hT ⟨w, hw, rfl⟩) x₁ q hq
  obtain ⟨k, hR'⟩ := (hC u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  obtain ⟨c', -⟩ := hR'.onto ()
  have hg1 : gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1
  have eU : Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
      Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := by rw [hg1]; rfl
  let yc : TC.GA B (B.R.N 0) := (((C.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c').1
  let xg : TC.GA B (B.R.N 0) := x'.1
  have hxg : xg ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := eU ▸ (((C.forms u).to0.cls0.lev.U_eq x'.1).1 x'.2).1
  have hyc : yc ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := eU ▸ (((C.forms u).cls 0 (Nat.zero_le _) (Or.inl rfl)).y c').2
  obtain ⟨p0, hp0, -⟩ := hR'.k_std ()
  have hk : k () ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) := hp0.uni
  obtain ⟨q', hq'⟩ : ∃ q' : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup I.mu0) u 0, TC.PtOf (yc * xg * k ()) q' :=
    GlobalTheory.Mem.Col2.ChiFinTop.exists_isPtOf_of_mem B.sp.cm I.twistPrimes_reference_tuple_eq_empty (mul_mem (mul_mem hyc hxg) hk)
  obtain ⟨hx', f'⟩ := stepZeroChartLevel_mem_columnLevel_of_stdBase I hI hPr u I.mu0 hR' c' (fun w hw =>
    hR'.k_off () _ (fun hT => Formalism.L2.Col.rls_T_notUnder hPr u _ hT ⟨w, hw, rfl⟩)
      (fun ⟨P, hP, _⟩ => by rw [I.twistPrimes_reference_tuple_eq_empty] at hP; exact Finset.notMem_empty _ hP) (Or.inl rfl)) x' q' hq'
  refine e₁.symm.trans (f₁.trans (Eq.trans (Eq.symm ?_) f'.symm))
  refine stepZeroColumnLevelType_eq_of_congruent_typePrimes I u _ _ fun w hw => ?_
  have hw' : w ∈ GlobalTheory.Mem.Col2.AdT.SBof I a := Finset.mem_union_left _ hw
  refine ⟨(I.cst a).D ⟨w, hw'⟩, (hI.idx_ok a).cst_ok.D_pos _, ?_⟩
  have h1 := hcg ⟨w, hw'⟩
  rw [(GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a (B.R.N 0) 0 ⟨w, hw'⟩ x.1).1, hxx] at h1
  exact h1

end GlobalTheory.Fam
end

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartCharacterEqMemberChartCharacterStdBStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroChartCharacter_eq_memberChartCharacter_stdBase : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (x : (A.K 0 (Nat.zero_le _) β).lev.U) (x' : (C.forms u).to0.cls0.lev.U), x.1 = x'.1 → (A.K 0 (Nat.zero_le _) β).lev.chi x = (C.forms u).to0.cls0.lev.chi x' := by
  first | exact @GlobalTheory.Fam.chi_zero_std | exact GlobalTheory.Fam.chi_zero_std | (intros; apply GlobalTheory.Fam.chi_zero_std <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormTransportedColumnStepZeroStandard
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.ZeroCongr
open Formalism.UG

theorem adFun_of_same {D : D7} {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {T f T' f' : ℕ}
    {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (S' : StepLevel D.host.F D.host.E (sigD D) J T' f' bad')
    (hU : ∀ x, x ∈ S.U ↔ x ∈ S'.U) (hchi : ∀ (x : S.U) (x' : S'.U), x.1 = x'.1 → S.chi x = S'.chi x')
    (Ψ) (hΨ : Ψ ∈ AdFun S' (embT D)) : Ψ ∈ AdFun S (embT D) := by
  intro γ hγ x x' κ h y y' hy
  rw [hchi κ ⟨κ.1, (hU _).1 κ.2⟩ rfl]
  exact hΨ γ hγ x x' ⟨κ.1, (hU _).1 κ.2⟩ h y y' hy


set_option maxHeartbeats 1000000 in
theorem rdS_congr (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (hn : V.rank = n)
    (J : Matrix (Fin n) (Fin n) D.host.E) (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f T' f' : ℕ}
    {bad bad' : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (S' : StepLevel D.host.F D.host.E (sigD D) J T' f' bad')
    {cl cl' : Type} (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (yc' : cl' → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (hb' : Function.Bijective (fun c => (Quotient.mk'' (yc' c) : Cls S')))
    (lam : D.what₂.Tau → DomWeight n) (φ) (φ') (hφ' : φ' ∈ FiC S' (embT D) lam yc')
    (hU : ∀ x, x ∈ S.U ↔ x ∈ S'.U) (hchi : ∀ (x : S.U) (x' : S'.U), x.1 = x'.1 → S.chi x = S'.chi x')
    (hrep : ∀ c, ∃ c', ∃ κ : S.U, (yc' c').1 = (yc c).1 * κ.1 ∧ S.chi κ = 1 ∧ φ c = φ' c')
    (y : Frames (gramC J (embT D))) (g : GA D V) :
    rdS θ V hn S yc φ y g = rdS θ V hn S' yc' φ' y g := by
  obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hφ'
  have hA' := (Submodule.mem_inf.1 hΨ).1
  have hA := adFun_of_same S S' hU hchi Ψ hA'
  have e : φ = fun c => Ψ (yc c) := by
    funext c z
    obtain ⟨c', κ, hy, hχ, hφc⟩ := hrep c
    rw [hφc]
    have h1 : IsTr (atInf (embT D) ((1 : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) z z := fun τ => by
      show z.1 τ = _ * z.1 τ
      simp [atInf]
    have e3 := hA 1 (Subgroup.one_mem _) (yc c) (yc' c') κ (by rw [map_one, one_mul]; try exact hy) z z h1
    show Ψ (yc' c') z = Ψ (yc c) z
    rw [e3, hχ, Units.val_one, one_mul]
  subst e
  obtain ⟨⟨x, hx⟩, hu, hv⟩ := GlobalTheory.AdForm.rdS_val D θ hθ V n hn J hJ T f bad S cl yc hb Ψ hA y g
  obtain ⟨-, -, hv'⟩ := GlobalTheory.AdForm.rdS_val D θ hθ V n hn J hJ T' f' bad' S' cl' yc' hb' Ψ hA' y g
  let z : Frames (gramC J (embT D)) :=
    ⟨fun τ => infM θ V hn g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (hu τ).mul (y.2 τ)⟩
  exact (hv x z hx (fun τ => rfl)).trans (hv' x z hx (fun τ => rfl)).symm

end GlobalTheory.AdForm.ZeroCongr

namespace GlobalTheory.Fam


set_option maxHeartbeats 4000000 in
theorem rd_zero_std : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ θ, IsInfFam θ → ∀ ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram, ∀ y, A.rd θ 0 (Nat.zero_le _) β ((I.rec7 l Z).e0Tw u a ψ₀) y = (GlobalTheory.Core.Mi.chart0 (C.forms u).to0).rd θ ψ₀ y := by
  intro B X I hI hP l Z C hC u a Ch A hA β hβ θ hθ ψ₀ hψ y
  unfold GlobalTheory.AdForm.TwDat.rd GlobalTheory.AdForm.Chart.rd GlobalTheory.Core.Mi.chart0
  dsimp only
  have hfr : ((C.forms u).to0.val0.eY y) = (⟨y.1, y.2⟩ : Frames (gramC (gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (embT (I.rec7 l Z)))) :=
    Subtype.ext ((hC u).eY 0 (Nat.zero_le _) (Or.inl rfl) y)
  rw [hfr]
  funext g
  refine GlobalTheory.AdForm.ZeroCongr.rdS_congr (I.rec7 l Z) θ hθ _ _ _ _ ?hJ _ _ _ _ (A.K 0 (Nat.zero_le _) β).y_bij ((C.forms u).to0.cls0.toChart.y_bij) (lamT u 0) _ _ ?hφ ?hU ?hchi ?hrep _ g
  case hJ => rfl
  case hφ => exact ((C.forms u).to0.val0.Fi ψ₀).1 (((I.rec7 l Z).fm u).Fi_zero ▸ hψ.1)
  case hU => exact GlobalTheory.T.stepZeroChartLevel_standardBasePoint_eq_member I hI hP l Z C hC u a Ch A hA β hβ
  case hchi => exact GlobalTheory.T.levelZeroChartCharacter_eq_memberChartCharacter_stdBase I hI hP l Z C hC u a Ch A hA β hβ
  case hrep =>
    intro c
    obtain ⟨κ, h1, h2⟩ := GlobalTheory.T.stepZero_representative_differs_by_level I hI hP l Z C hC u a Ch A hA β hβ c
    refine ⟨(I.eCls0 l u a).symm c.1, κ, h1, h2, ?_⟩
    funext z
    have hz : (C.forms u).to0.val0.eY.symm z = ⟨z.1, z.2⟩ := by
      apply (C.forms u).to0.val0.eY.injective
      rw [Equiv.apply_symm_apply]
      exact Subtype.ext ((hC u).eY 0 (Nat.zero_le _) (Or.inl rfl) _).symm
    rw [hz]
    rfl

end GlobalTheory.Fam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormTransportedColumnStepZeroStandardStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarForm_transportedColumn_stepZero_standard : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ θ, IsInfFam θ → ∀ ψ₀ ∈ ((I.rec7 l Z).mem u).A.Mram, ∀ y, A.rd θ 0 (Nat.zero_le _) β ((I.rec7 l Z).e0Tw u a ψ₀) y = (GlobalTheory.Core.Mi.chart0 (C.forms u).to0).rd θ ψ₀ y := by
  first | exact @GlobalTheory.Fam.rd_zero_std | exact GlobalTheory.Fam.rd_zero_std | (intros; apply GlobalTheory.Fam.rd_zero_std <;> assumption)
end
