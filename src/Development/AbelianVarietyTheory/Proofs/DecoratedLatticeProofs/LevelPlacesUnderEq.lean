module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqScaleAtResidueChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorLevelMultiplicitySpaceMemGoodRows
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct Pointwise

namespace GlobalTheory.ProjLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem not_isConjPl_of_div {D : D7} (P : Formalism.L2.Host.PiBar D.host) {k k' : Fin 2} {w w' : Pl D.host.E}
    (hw : P.Div k w) (hw' : P.Div k' w') : ¬ Formalism.IndefR.Lev.IsConjPl w w' := by
  intro hc
  have hov : ∀ {j : Fin 2} {u : Pl D.host.E}, P.Div j u → ((D.host.g j : ℕ) : 𝓞 D.host.E) ∈ u.asIdeal := by
    intro j u hu
    have h1 := P.pb_over j
    rw [← hu] at h1
    have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g j : ℕ) : 𝓞 D.host.K) ∈ u.asIdeal := h1
    rwa [map_natCast] at this
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hz, hzv⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext (hzv.trans ((bridge_star_holds D.R D.host _).trans
      (D.host.conj.apply_symm_apply (y : D.host.E))))
    exact e ▸ hz
  have hmax : (D.host.conj • w.asIdeal).IsMaximal := by
    have := w.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => w.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have heq : D.host.conj • w.asIdeal = w'.asIdeal := hmax.eq_of_le w'.isPrime.ne_top hle
  have hm := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w (hov hw)).2.2.2
    (P.pb k) (P.pb_over k) w' ((GlobalTheory.Mem.Chr.conjPl_iff_smul D.host.conj w w').2 heq)
  have hg : D.host.g k = D.host.g k' :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w' hm.1).1.symm.trans
      (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k') (D.host.g_prime k') (D.nd.g_split k') w' (hov hw')).1
  obtain rfl : k = k' := by
    have := D.host.g_ne
    fin_cases k <;> fin_cases k' <;> first | rfl | exact absurd hg this | exact absurd hg.symm this
  exact hm.2.1 hw hw'

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

end

end GlobalTheory.ProjLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.PlaceSep

variable {D : D7}

theorem natCast_mem_of_under_eq {PP PP' : Pl D.host.E}
    (h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) {n : ℕ} (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) :
    ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  have h1 : ((n : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F) ∈ PP.asIdeal
    rwa [map_natCast]
  rw [h] at h1
  have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (n : 𝓞 D.host.F) ∈ PP'.asIdeal := h1
  rwa [map_natCast] at h2

theorem not_two_primes_mem (PP : Pl D.host.E) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h1 : ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (h2 : ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : False := by
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
  have e : (u : 𝓞 D.host.E) * ((p : ℕ) : 𝓞 D.host.E) + (v : 𝓞 D.host.E) * ((q : ℕ) : 𝓞 D.host.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
    push_cast at this
    exact this
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem twist_prime {gp : Fin 2 → ℕ} {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces gp Q) {PP : Pl D.host.E} (hP : PP ∈ Q) :
    ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ∀ i, q ≠ gp i := by
  obtain ⟨⟨q, hq, hc, -, hne⟩, -⟩ := hQ PP hP
  refine ⟨q, hq, ?_, hne⟩
  have := Ideal.absNorm_mem PP.asIdeal
  rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply, show Nat.card (𝓞 D.host.E ⧸ PP.asIdeal) = q from hc] at this

theorem g_mem_of_div (P : Formalism.L2.Host.PiBar D.host) {k : Fin 2} {w : Pl D.host.E} (hw : P.Div k w) :
    ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
  have h1 := P.pb_over k
  rw [← hw] at h1
  have : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ w.asIdeal := h1
  rwa [map_natCast] at this

end GlobalTheory.Fam.PlaceSep


open GlobalTheory.Fam.PlaceSep in
theorem GlobalTheory.Fam.pg_qAll_under_inj : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ PP PP' : Pl D.host.E, (PP ∈ (pk W).Pg ∨ QAll W PP) → (PP' ∈ (pk W).Pg ∨ QAll W PP') → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
  intro D L hT Gi Gl Kc Yd cX ex W hP PP PP' hPP hPP' hu
  have hL : (pk W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev

  have mixed : ∀ A B : Pl D.host.E, A ∈ (pk W).Pg → QAll W B → A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → False := by
    intro A B hA hB hAB
    obtain ⟨k, hk⟩ := (hL.Pg A).1 hA
    obtain ⟨t, ht⟩ := hB
    obtain ⟨q, hq, hqB, hne⟩ := twist_prime (hL.Q_pl t) ht
    exact not_two_primes_mem B (D.host.g_prime k) hq (hne k).symm
      (natCast_mem_of_under_eq hAB (g_mem_of_div _ hk)) hqB
  rcases hPP with h1 | h1 <;> rcases hPP' with h2 | h2
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 h1
    obtain ⟨k', hk'⟩ := (hL.Pg PP').1 h2
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with e | e
    · exact e
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 e) (GlobalTheory.ProjLift.not_isConjPl_of_div _ hk' hk)
  · exact (mixed PP PP' h1 h2 hu).elim
  · exact (mixed PP' PP h2 h1 hu.symm).elim
  · exact hP.sel PP PP' h1 h2 hu
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesUnderEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_places_under_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ PP PP' : Pl D.host.E, (PP ∈ (pk W).Pg ∨ QAll W PP) → (PP' ∈ (pk W).Pg ∨ QAll W PP') → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
  first | exact @GlobalTheory.Fam.pg_qAll_under_inj | exact GlobalTheory.Fam.pg_qAll_under_inj | (intros; apply GlobalTheory.Fam.pg_qAll_under_inj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReferenceTupleOffPrimesEmpty
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SameCosetOfMemCosetIn
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue.Cl


open Classical in
theorem sameCoset_of_mem_cosetIn {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p : PtAt R sel mu cst u j)
    (h : j + 1 = R.m) (P : rowSG Pr sel mu) {z z' : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P) (hz' : z' ∈ cosetIn p P) :
    SameCoset sel mu cst P z z' := by
  obtain ⟨w, hw, hzw⟩ := hz
  obtain ⟨w', hw', hzw'⟩ := hz'
  obtain ⟨y, -, hY⟩ := p.mem_ybSet h
  rw [hY] at hw hw'
  have hww : w - w' ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
    have e1 : w - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := hw
    have e2 : w' - y ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := hw'
    have := sub_mem e1 e2
    rwa [sub_sub_sub_cancel_right] at this
  have h1 := (mem_locLat _ _ _ _).1 hww P
  set F := frsF sel mu p.1.1 P with hF
  set c : X.E := ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ with hc
  have hc' : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ = c := by
    rw [hc]; split_ifs <;> simp
  simp only [hc'] at h1
  have hFm : ∀ x, F x ∈ p.1.1.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
    intro x
    rw [hF]
    unfold frsF
    split_ifs with hP
    · exact (Deco.liftFr_spec (Deco.Ok.hasLift p.1.1.deco.2 ⟨P.1, hP⟩)).1 x
    · exact p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left hP⟩ x
  have h2 : c • (F.symm w - F.symm w') ∈ stdAt X.E (R.N j) P.1 := by
    rw [← map_sub, ← map_smul]
    apply (hFm _).1
    rw [LinearEquiv.apply_symm_apply]
    exact h1
  have h3 : c • (z - z') = c • (z - F.symm w) - c • (z' - F.symm w') + c • (F.symm w - F.symm w') := by
    rw [← smul_sub, ← smul_add]
    congr 1
    abel
  have h4 : c • (z - z') ∈ stdAt X.E (R.N j) P.1 := by
    rw [h3]
    exact add_mem (sub_mem hzw hzw') h2
  intro l
  have h5 := (ciMem_stdAt _ _).1 h4 l
  rw [Pi.smul_apply, smul_eq_mul] at h5
  exact h5

end GlobalTheory.TwU.AtTrue.Cl

namespace GlobalTheory.TwU.AtTrue.Cl

end GlobalTheory.TwU.AtTrue.Cl
end

noncomputable section

namespace GlobalTheory.AdForm.Keep

section Local

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped Classical

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word}

theorem res_of_xiAt {n : ℕ} (h : n + 2 = R.m) (hs : cst.sharp = true) (hh : ∀ (al : L.β n) P, P.1 ∈ Pr.vGs → L.h n al P = 1)
    {b : Idx sel mu L n} {b' : Idx sel mu L (n + 1)} {p : PtAt R sel mu cst u n} {p' : PtAt R sel mu cst u (n + 1)}
    (hx : xiAt Ch sel mu cst L u n b b' p p' ≠ 0) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (l : Fin (R.N (n + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) * (frsF sel mu p'.1.1 P).symm (repY p'.1.2) l) ∧
      redP P.1 ((qOf P.1 : X.E) * (frsF sel mu p'.1.1 P).symm (repY p'.1.2) l) = if l.1 = R.k then 1 else 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hx
  rw [xiAt_penultimate_eq_xiCpl1 Ch sel mu cst L h (b.some_get (by omega)).symm] at hx
  have h1 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) P (Finset.mem_univ _)
  rw [hh _ P hP] at h1
  exact oneYbSym_of_m Ch sel mu cst h.symm hs P hP _ _ h1 l

end Local

section True

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC
open scoped Classical
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} {I : TC B X}


open GlobalTheory.GO.ChSrc (trueWt nuEnd sS sD polFn fnPol) in
open _root_.Formalism.L2.Forms (fnOf shiftOf ValC) in
theorem kmap_mem_valC {X : Fields} {R : Ranks} (I : ChainIn X.E X.K X.Tau R) (σ : X.K →+* ℂ) (h : I.Ok) (hc : X.Tau → HCParam R) {i : ℕ}
    (hi : i < R.m) (c : (I.S i).Cl) (c' : (I.S (i + 1)).Cl) (J : (DVar X.Tau (R.N i) (R.N (i + 1)) →₀ ℕ) → ℂ)
    (e : I.jet i c c' = jetMap J 0) (f : Fr X.emb σ (R.N i) → ℂ) (hf : f ∈ ValC (Gr X.emb σ (R.N i)) (trueWt hc i)) :
    (I.chain X.emb σ h hc).Kmap i c c' f ∈ ValC (Gr X.emb σ (R.N (i + 1))) (trueWt hc (i + 1)) := by
  obtain ⟨P, hP, rfl⟩ := hf
  rw [ValTie.cspan_eq] at hP
  have hN : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [add_mul]; omega
  have hV : jetMap J (nuEnd hc i) P ∈ Formalism.L2.DIV.VV ℂ (trueWt hc (i + 1)) := by
    refine GlobalTheory.JetPoint.jetMap_mem hN.le _ _ _ (fun ap => ?_) J
    refine GlobalTheory.SubstMem.substAdj_sharp_mem ℂ X.Tau _ _ hN _ _ (sD hc i) (sS hc i) _
      ⟨fun τ a => ?_, fun τ j hj => GlobalTheory.GO.ChSrc.trueWt_new hc hi τ j (not_lt.mpr hj), GlobalTheory.GO.ChSrc.nuEnd_cast hc hi⟩ ap _ hP
    have := GlobalTheory.GO.ChSrc.trueWt_old hc hi τ (Fin.castLE hN.le a) a.2
    simp only [Fin.val_castLE, Fin.eta] at this
    omega
  have ap : ∀ {n : ℕ} (s : X.Tau → ℤ) (Q : Formalism.L2.DIV.Pol ℂ X.Tau n) (y : Fr X.emb σ n),
      fnOf (Gr X.emb σ n) s 1 Q y = (∏ τ, (y.1 τ).det ^ s τ) * MvPolynomial.eval (fun v => y.1 v.1 v.2.1 v.2.2) Q := by
    intro n s Q y
    simp [fnOf]
  have h1 : (I.chain X.emb σ h hc).sharp i (fnOf (Gr X.emb σ (R.N i)) (shiftOf (trueWt hc i)) 1 P) =
      polFn X σ _ (P * ∏ τ, frDet ℂ (R.N i) τ ^ nuEnd hc i τ) := by
    funext (y : Fr X.emb σ (R.N i))
    have hd : ∀ τ, MvPolynomial.eval (fun v : X.Tau × Fin (R.N i) × Fin (R.N i) => y.1 v.1 v.2.1 v.2.2)
        (frDet ℂ (R.N i) τ) = (y.1 τ).det := fun τ => by
      rw [frDet, RingHom.map_det]
      congr 1
      ext a b
      simp
    show (∏ τ, (y.1 τ).det ^ (I.chain X.emb σ h hc).sSharp i τ) * fnOf (Gr X.emb σ (R.N i)) (shiftOf (trueWt hc i)) 1 P y = _
    rw [ap, GlobalTheory.GO.ChSrc.polFn_apply, map_mul, map_prod, ← mul_assoc, ← Finset.prod_mul_distrib, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, hd, ← zpow_natCast, GlobalTheory.GO.ChSrc.nuEnd_cast hc hi, zpow_add₀ (isUnit_det_fr y τ).ne_zero,
      (GlobalTheory.LvT.Built.KMap.sSharp_eq I σ h hc hi τ).1, mul_comm]
    rfl
  have h2 : jetMap J 0 (P * ∏ τ, frDet ℂ (R.N i) τ ^ nuEnd hc i τ) = jetMap J (nuEnd hc i) P := by
    simp [jetMap]
  refine ⟨(I.rho i c * I.rho' i c') • jetMap J (nuEnd hc i) P, ?_, ?_⟩
  · rw [ValTie.cspan_eq]
    exact Submodule.smul_mem _ _ hV
  funext (y : Fr X.emb σ (R.N (i + 1)))
  show _ = (I.rho i c * I.rho' i c') * ((∏ τ, (y.1 τ).det ^ (I.chain X.emb σ h hc).sDiv i τ)⁻¹ *
    polFn X σ _ (I.jet i c c' (fnPol X σ _ ((I.chain X.emb σ h hc).sharp i
      (fnOf (Gr X.emb σ (R.N i)) (shiftOf (trueWt hc i)) 1 P)))) y)
  rw [h1, GlobalTheory.GO.ChSrc.fnPol_polFn, e, h2, ap, MvPolynomial.smul_eval, GlobalTheory.GO.ChSrc.polFn_apply, mul_left_comm,
    ← Finset.prod_inv_distrib]
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [(GlobalTheory.LvT.Built.KMap.sSharp_eq I σ h hc hi τ).2, ← zpow_neg, ← GlobalTheory.GO.ChSrc.trueWt_detShift_succ hc hi]
  rfl

theorem kmap_val (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m)
    (c : (I.stp u a i).Cl) (c' : (I.stp u a (i + 1)).Cl) (f : Fr B.fields.emb B.embLL (B.R.N i) → ℂ)
    (hf : f ∈ Formalism.L2.Forms.ValC (Gr B.fields.emb B.embLL (B.R.N i)) (lamT (B.hcW u) i)) :
    (I.chain l u a).Kmap i c c' f ∈ Formalism.L2.Forms.ValC (Gr B.fields.emb B.embLL (B.R.N (i + 1))) (lamT (B.hcW u) (i + 1)) :=
  kmap_mem_valC (X := B.fields) (I.chIn u a) B.embLL (l.ch u a) (B.hcW u) hi c c' _ rfl f hf

end True

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links _root_.Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.AdForm.Keep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBasePointCarryingLatticeAndFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBasePointCarryingLatticeAndFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.BasePoint

variable {D : D7}

theorem algebraMap_placeIdem_mem {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    algebraMap (AF D.host.F) (AE D) ε ∈ idAt D (· = v) := by
  obtain ⟨α, rfl, -, h0⟩ := hε
  obtain ⟨hinf, hcomp⟩ := placeIdempotent_infinite_and_finite_components D v _ α rfl
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
  refine ⟨hinf, fun w hw => ?_⟩
  rw [hcomp, h0 w hw, TensorProduct.zero_tmul]

theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D Q := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
  exact ⟨ha.1, fun w hw => ha.2 w (fun hp => hw (h w hp))⟩

theorem mulVec_mem' {I : Ideal (AE D)} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ I) : ∀ i, (A *ᵥ y) i ∈ I := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => I.mul_mem_left _ (hy j)

theorem mulVec_fix {V : HSp D} {e : AE D} {ε : AF D.host.F} {u v : Pl D} (hε : IsPlaceIdem D u ε)
    (he : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) {h : GA D V} (hs : SuppAt e V h) (huv : v ≠ u)
    {y : Fin V.rank → AE D} (hy : ∀ l, y l ∈ idAt D (· = v)) : mt V h *ᵥ y = y := by
  have hz : ∀ l, algebraMap (AF D.host.F) (AE D) ε * y l = 0 := fun l =>
    (placeIdem_acts D u ε hε).2 _ (idAt_mono (fun w hw => by rw [hw]; exact huv) (hy l))
  have h1 : (mt V h - 1) *ᵥ y = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    calc (mt V h - 1) i j * y j = (algebraMap (AF D.host.F) (AE D) ε * (mt V h - 1) i j) * y j := by
          rw [← he, hs i j]
      _ = (mt V h - 1) i j * (algebraMap (AF D.host.F) (AE D) ε * y j) := by ring
      _ = 0 := by rw [hz j, mul_zero]
  calc mt V h *ᵥ y = ((mt V h - 1) + 1) *ᵥ y := by rw [sub_add_cancel]
    _ = y := by rw [Matrix.add_mulVec, h1, Matrix.one_mulVec, zero_add]

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem pr_e_mul (q : SplitPt D k) (a : AE D) : q.pr (q.e * a) = q.pr a := by
  rw [← q.sec_pr a, q.pr_sec]

theorem e_mul_eps (q : SplitPt D k) {ε : AF D.host.F} (he : q.e + cA D q.e = algebraMap (AF D.host.F) (AE D) ε) :
    q.e * algebraMap (AF D.host.F) (AE D) ε = q.e := by
  rw [← he, mul_add, q.split.1, q.split.2.1, add_zero]

theorem map_mt_eq_one (q : SplitPt D k) (q' : SplitPt D k') (hne : q.v ≠ q'.v) {V : HSp D} {h : GA D V}
    (hs : SuppAt q'.e V h) : (mt V h).map (GlobalTheory.LocMod.ofSplit q).π = 1 := by
  show (mt V h).map q.pr = 1
  obtain ⟨ε, hε, he⟩ := q.above
  obtain ⟨ε', hε', he'⟩ := q'.above
  have h0 : q.pr (algebraMap (AF D.host.F) (AE D) ε') = 0 := by
    rw [← pr_e_mul, ← e_mul_eps q he, mul_assoc,
      (placeIdem_acts D q.v ε hε).2 _ (idAt_mono (fun w hw => by rw [hw]; exact Ne.symm hne)
        (algebraMap_placeIdem_mem hε')), mul_zero, map_zero]
  ext i j
  have hij := hs i j
  rw [he'] at hij
  have h1 : q.pr ((mt V h - 1) i j) = 0 := by rw [← hij, map_mul, h0, zero_mul]
  have e2 : (mt V h) i j = (mt V h - 1) i j + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := by simp
  rw [Matrix.map_apply, e2, map_add (f := _), h1, zero_add]
  by_cases hij' : i = j <;> simp [Matrix.one_apply, hij']

theorem xi_ne (q : SplitPt D k) : (GlobalTheory.LocMod.ofSplit q).xi ≠ 0 := by
  unfold GlobalTheory.LocMod.Place.xi GlobalTheory.LocMod.Place.pr
  intro h0
  have h1 : (GlobalTheory.LocMod.ofSplit q).π (incA D D.host.xi0) * (GlobalTheory.LocMod.ofSplit q).π (incA D D.host.xi0⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem latV_iff_hat' (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D) (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.hat L :=
  ⟨GlobalTheory.T.latticeCompletionAtPlaces_mem_completedHermitianLattice D S L P y, GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice D S L P y hy⟩

theorem finE_mulVec' (S : HSp D) (x : GA D S) (y : Fin S.rank → AE D) :
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((mt S x *ᵥ y) i))) =
      (Formalism.IndefR.Lev.finE S x).val *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) := by
  have h : ((Formalism.IndefR.Lev.finE S x).val) = (mt S x).map ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) := by
    ext i j
    rfl
  rw [h]
  ext i
  exact RingHom.map_mulVec ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)) (mt S x) y i

theorem exists_base (V : HSp D) (Λ L₀ : Lat V) (hΛ : IsSelfDualC V Λ) (hL₀ : IsSelfDualC V L₀) :
    ∃ t₀ ∈ GfC V, ∀ P, Moves V t₀ Λ L₀ P := by
  obtain ⟨t₀, ht₀, htr⟩ := (GlobalTheory.AdIsom.adelicIsometries D).2.2.1 V V (LinearEquiv.refl _ _) (fun _ _ => rfl) Λ L₀ hΛ hL₀
    ∅ (by intro w hw; simp at hw) 0 (fun _ => 0) (fun _ => 0) (by simp) (by simp)
  rw [LinearEquiv.refl_toLinearMap, GlobalTheory.AdIsomCorrection.mA_id, Matrix.mul_one] at htr
  refine ⟨t₀, ht₀, fun P y hy => ?_⟩
  rw [latV_iff_hat' V Λ P y hy, latV_iff_hat' V L₀ P _ (mulVec_mem' _ hy), finE_mulVec']
  exact htr.2.1 _

variable {J : Type} [Fintype J] {kk : J → Type} [∀ i, Field (kk i)] [∀ i, ValuativeRel (kk i)]
  [∀ i, TopologicalSpace (kk i)] [∀ i, IsNonarchimedeanLocalField (kk i)]

theorem exists_corr (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (q : ∀ i, SplitPt D (kk i))
    (hinj : Function.Injective (fun i => (q i).v)) (M : ∀ i, GL (Fin V.rank) (kk i)) (t₀ : GA D V) (s : Finset J) :
    ∃ g ∈ GfC V, (∀ v, (∀ i, v ≠ (q i).v) → ∀ y : Fin V.rank → AE D, (∀ l, y l ∈ idAt D (· = v)) → mt V g *ᵥ y = y) ∧
      ∀ i ∈ s, GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (q i)) V (g * t₀) β (M i).val := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, one_mem _, fun v _ y _ => by rw [mt_one, Matrix.one_mulVec], fun i hi => by simp at hi⟩
  | insert j s hj ih =>
    obtain ⟨g, hg, hfix, hmv⟩ := ih
    obtain ⟨h, hsupp, hmove⟩ :=
      (GlobalTheory.T.exists_normal_frames_and_base_point_split_place D (kk j) (GlobalTheory.LocMod.ofSplit (q j)) (xi_ne (q j))).2.2 V β (M j) (g * t₀)
    refine ⟨h * g, mul_mem (GlobalTheory.WeilProduct.mem_GfC_of_suppAt (q j).split hsupp) hg, ?_, ?_⟩
    · intro v hv y hy
      rw [mt_mul, ← Matrix.mulVec_mulVec, hfix v hv y hy]
      obtain ⟨ε, hε, he⟩ := (q j).above
      exact mulVec_fix hε he hsupp (hv j) hy
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · rw [mul_assoc]; exact hmove
      · intro b hb
        have hij : (q i).v ≠ (q j).v := fun h' => hj (by rw [← (hinj h' : i = j)]; exact hi)
        rw [mul_assoc, mt_mul, Matrix.mul_assoc, Matrix.map_mul, map_mt_eq_one (q i) (q j) hij hsupp, Matrix.one_mul]
        exact hmv i hi b hb

end GlobalTheory.FinPl.BasePoint


open GlobalTheory.FinPl.BasePoint in
theorem GlobalTheory.FinPl.BasePoint.exists_move : ∀ (D : D7) (V : HSp D) (Λ L₀ : Lat V) (β : GL (Fin V.rank) (Lev.EAf D)), IsSelfDualC V Λ → IsSelfDualC V L₀ → ∀ (J : Type) [Fintype J] (k : J → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ M : ∀ i, GL (Fin V.rank) (k i), ∃ t ∈ GfC V, ∃ L : Lat V, IsSelfDualC V L ∧ (∀ P, Moves V t Λ L P) ∧ (∀ v, (∀ i, v ≠ (q i).v) → latV V L (· = v) = latV V L₀ (· = v)) ∧ ∀ i, GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (q i)) V t β (M i).val := by
  intro D V Λ L₀ β hΛ hL₀ J _ kk _ _ _ _ q hinj M
  obtain ⟨t₀, ht₀, hmv₀⟩ := exists_base V Λ L₀ hΛ hL₀
  obtain ⟨g, hg, hfix, hmv⟩ := exists_corr V β q hinj M t₀ Finset.univ
  obtain ⟨L, hL, hmoves⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D V Λ hΛ).1 (g * t₀)
  refine ⟨g * t₀, mul_mem hg ht₀, L, hL, hmoves, ?_, fun i => hmv i (Finset.mem_univ i)⟩
  intro v hv
  ext y
  by_cases hy : ∀ l, y l ∈ idAt D (· = v)
  · have hz : ∀ l, (mt V t₀⁻¹ *ᵥ y) l ∈ idAt D (· = v) := mulVec_mem' _ hy
    have h1 : mt V t₀ *ᵥ (mt V t₀⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, ← mt_mul, mul_inv_cancel, mt_one, Matrix.one_mulVec]
    have h2 : mt V (g * t₀) *ᵥ (mt V t₀⁻¹ *ᵥ y) = y := by
      rw [mt_mul, ← Matrix.mulVec_mulVec, h1, hfix v hv y hy]
    have a1 := hmoves (· = v) _ hz
    have a2 := hmv₀ (· = v) _ hz
    rw [h2] at a1
    rw [h1] at a2
    exact a1.symm.trans a2
  · have hsupp : ∀ (N : Lat V), IsSelfDualC V N → y ∉ latV V N (· = v) := fun N hN hyN =>
      hy (((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).2 V).2.2.2 N y hN.1 |>.1 hyN).1
    exact iff_of_false (hsupp L hL) (hsupp L₀ hL₀)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBasePointCarryingLatticeAndFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_point_carrying_lattice_and_frames : ∀ (D : D7) (V : HSp D) (Λ L₀ : Lat V) (β : GL (Fin V.rank) (Lev.EAf D)), IsSelfDualC V Λ → IsSelfDualC V L₀ → ∀ (J : Type) [Fintype J] (k : J → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ M : ∀ i, GL (Fin V.rank) (k i), ∃ t ∈ GfC V, ∃ L : Lat V, IsSelfDualC V L ∧ (∀ P, Moves V t Λ L P) ∧ (∀ v, (∀ i, v ≠ (q i).v) → latV V L (· = v) = latV V L₀ (· = v)) ∧ ∀ i, GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (q i)) V t β (M i).val := by
  first | exact @GlobalTheory.FinPl.BasePoint.exists_move | exact GlobalTheory.FinPl.BasePoint.exists_move | (intros; apply GlobalTheory.FinPl.BasePoint.exists_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfMemCompletedHomLatticeIffLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfMemCompletedHomLatticeIffLocal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.HalfLat
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_den {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e P) {r : D.host.E}
    (hr : finPart D (e * incA D r) ∈ intAE D) :
    ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 D.host.E, (o : D.host.E) = s * r := by
  rcases (P.valuation D.host.E).val_le_one_or_val_inv_lt_one r with h | h
  · obtain ⟨n, d, hd⟩ := P.exists_primeCompl_mul_eq_of_integer r h
    exact ⟨d, d.2, n, by rw [mul_comm]; exact hd.symm⟩
  by_cases hr0 : r = 0
  · exact ⟨1, P.asIdeal.primeCompl.one_mem, 0, by simp [hr0]⟩
  obtain ⟨n, d, hd⟩ := P.exists_primeCompl_mul_eq_of_integer r⁻¹ h.le
  have hdP : (d : 𝓞 D.host.E) ∉ P.asIdeal := d.2
  have hd0 : (d : 𝓞 D.host.E) ≠ 0 := fun h => hdP (h ▸ zero_mem _)
  have hd0' : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun h => hd0 (RingOfIntegers.ext h)
  have hd' : r⁻¹ * ((d : 𝓞 D.host.E) : D.host.E) = (n : D.host.E) := hd
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (inv_ne_zero hr0) hd0' hd'
  have hnP : n ∈ P.asIdeal := by
    refine (P.valuation_lt_one_iff_mem (K := D.host.E) n).1 ?_
    change P.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E n) < 1
    rw [← hd, Valuation.map_mul]
    exact mul_lt_one_of_lt_of_le h (P.valuation_le_one _)
  have h1 : finPart D (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hdP ((he.2 _ hd0).2 h)
  refine absurd ?_ ((he.2 _ hn0).1 hnP)
  have h2 := GlobalTheory.HeckeConj.mul_mem_intAE D hr h1
  rwa [← RingHom.map_mul, mul_mul_mul_comm, he.1.1, ← RingHom.map_mul, ← inv_inv r, ← mul_inv, hd'] at h2

noncomputable def form (S : HSp D) (s : Fin S.rank → D.host.E) : (Fin S.rank → D.host.E) →ₗ[D.host.E] D.host.E :=
  ∑ i, ∑ j, (star (s i) * S.gram i j) • LinearMap.proj j

theorem form_apply (s v : Fin S.rank → D.host.E) : form S s v = ∑ i, ∑ j, star (s i) * S.gram i j * v j := by
  simp [form, LinearMap.sum_apply]

theorem expand {n : ℕ} {s s' : Fin n → Fin S.rank → D.host.E}
    (h : ∀ a j, ∑ i, s i a * ∑ k, star (s' i k) * S.gram k j = if a = j then 1 else 0) (v : Fin S.rank → D.host.E) :
    v = ∑ k, form S (s' k) v • s k := by
  funext a
  have h1 : v a = ∑ j, (∑ i, s i a * ∑ k, star (s' i k) * S.gram k j) * v j := by simp [h]
  rw [h1, Finset.sum_apply]
  simp only [form_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

noncomputable def coefA (S T : HSp D) (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    WO S T →+ AE D :=
  AddMonoidHom.mk' (fun u => ∑ i, ∑ j, ∑ m, incA D (b * (star (t i) * T.gram i j) * s m) * u j m) fun x y => by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem coefA_apply (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) (u : WO S T) :
    coefA S T b s t u = ∑ i, ∑ j, ∑ m, incA D (b * (star (t i) * T.gram i j) * s m) * u j m := rfl

theorem coefA_int (hN : IsSelfDualC S N) (hN' : IsSelfDualC T N') {b : D.host.E}
    (hb : ∀ a ∈ D.host.AA, ∃ c : 𝓞 D.host.E, (c : D.host.E) = a * b)
    {s : Fin S.rank → D.host.E} (hs : s ∈ N) {t : Fin T.rank → D.host.E} (ht : t ∈ N') {u : WO S T}
    (hu : u ∈ latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) :
    finPart D (coefA S T b s t u) ∈ intAE D := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s0, hs0, t0, ht0, rfl⟩ := hw
    obtain ⟨c, hc'⟩ := hb a ha
    obtain ⟨o, ho⟩ := (hN.2 s).1 hs s0 hs0
    obtain ⟨o', ho'⟩ := (hN'.2 t0).1 ht0 t ht
    refine AddSubgroup.subset_closure ⟨α, hα, c * o' * o, ?_⟩
    have h1 : ∀ x y : D.host.E, incA D x * (pairA D.host.F 0 α ⊗ₜ[D.host.F] y) =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] (x * y) := fun x y => by
      change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : ((c * o' * o : 𝓞 D.host.E) : D.host.E) = ∑ i, ∑ j, ∑ m, (b * (star (t i) * T.gram i j) * s m) *
        (a * t0 j * ∑ k, star (s0 k) * S.gram k m) := by
      have h3 : ((c * o' * o : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) * o' * o := by
        simp only [map_mul]
      rw [h3, hc', ho, ho', Finset.sum_comm (f := fun i j => star (s0 i) * S.gram i j * s j), Finset.mul_sum (a := a * b),
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum (a := a * b), Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_mul]
      ring
    rw [coefA_apply]
    simp only [Matrix.of_apply, h1, ← TensorProduct.tmul_sum]
    rw [h2]
    rfl
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), RingHom.map_add (f := _)]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, RingHom.map_neg]; exact neg_mem hx

theorem coefA_rat (e : AE D) (b : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E)
    (x : Formalism.L2.Col.HomE D.host.E S.rank T.rank) :
    coefA S T b s t ((LinearMap.toMatrix' x).map fun r => e * incA D r) = e * incA D (b * form T t (x s)) := by
  rw [coefA_apply, form_apply, ← LinearMap.toMatrix'_mulVec x s]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Matrix.map_apply, mul_left_comm, ← RingHom.map_mul]
  congr 2
  ring


set_option maxHeartbeats 1000000 in
theorem mem_localization_of_component (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) (hN' : IsSelfDualC T N') {e e' : AE D}
    {P : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e' P) (hee : e' * e = e')
    {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : ((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S N hN
  obtain ⟨m, t, t', ht, htt⟩ := GlobalTheory.LatVacDual.dualFamily D T N' hN'
  have hxe : x = ∑ k, ∑ i, form T (t' i) (x (s k)) • (form S (s' k)).smulRight (t i) := by
    refine LinearMap.ext fun v => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [expand hss v, map_sum]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_lhs => rw [map_smul, expand htt (x (s k)), Finset.smul_sum]
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D)
  have h1 : (1 : D.host.E) ∈ D.host.AA0 * (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [Formalism.BasicNotions.Host.AA0, inv_mul_cancel₀ hb0]
    exact FractionalIdeal.one_mem_one _
  rw [← one_smul D.host.E x]
  refine FractionalIdeal.mul_induction_on (C := fun c => c • x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
    (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) h1 (fun a ha b hb => ?_)
    fun a b ha hb => by rw [add_smul]; exact add_mem ha hb
  have hb' : ∀ a ∈ D.host.AA, ∃ c : 𝓞 D.host.E, (c : D.host.E) = a * b := fun a ha => by
    rw [Formalism.BasicNotions.Host.AA, Formalism.BasicNotions.Host.ccE, hc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul] at ha
    have h := FractionalIdeal.mul_mem_mul ha hb
    rw [Formalism.BasicNotions.Host.AA0, inv_mul_cancel₀ hb0] at h
    exact (FractionalIdeal.mem_one_iff _).1 h
  have hi : finPart D e' ∈ intAE D := by
    by_contra h
    refine P.asIdeal.primeCompl.one_mem ((he.2 1 one_ne_zero).2 ?_)
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one]
  rw [hxe, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [Finset.smul_sum]
  refine sum_mem fun i _ => ?_
  have h2 := GlobalTheory.HeckeConj.mul_mem_intAE D hi (coefA_int hN hN' hb' (hs k).1 (ht i).2 hx)
  rw [coefA_rat, ← RingHom.map_mul, ← mul_assoc, hee] at h2
  obtain ⟨d, hd, o, ho⟩ := exists_den he h2
  refine ⟨d, hd, ?_⟩
  have h3 : a • (form S (s' k)).smulRight (t i) ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
    refine Submodule.subset_span ⟨a, ha, _, fun v hv => ?_, rfl⟩
    obtain ⟨c, hc⟩ := (hN.2 v).1 hv _ (hs k).2
    rw [LinearMap.smulRight_apply, form_apply, ← hc]
    exact N'.smul_mem c (ht i).1
  convert Submodule.smul_mem _ o h3 using 1
  rw [← IsScalarTower.algebraMap_smul D.host.E d, ← IsScalarTower.algebraMap_smul D.host.E o,
    show algebraMap _ D.host.E o = _ from ho, smul_smul, smul_smul, smul_smul]
  congr 1
  change (d : D.host.E) * _ * _ = _
  ring

theorem comp_mem (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : s ∉ P.asIdeal := hs
  have hne : s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (RingOfIntegers.ext h)
  have h1 : finPart D (e * incA D ((s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ h1 _
    (finTens_mem_latO (one_mem_intAf _) (HalfPairing.toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  have h5 := GlobalTheory.SplitScalar.infPart_splitIdem he.1
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h5, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem half_mem_latO_iff : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) := by
  intro D S T hc e SS he N N' hN hN' x
  constructor
  · intro hx P hP
    obtain ⟨a, ha, hae⟩ := GlobalTheory.OffIdem.idemSum_mul_idemAt he hP
    exact mem_localization_of_component hc hN hN' ha hae hx
  · intro hx
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
    have e1 : ((LinearMap.toMatrix' x).map fun r => (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' x).map fun r => es PP * incA D r : WO S T) := by
      ext i j
      rw [Matrix.map_apply, Matrix.sum_apply, Finset.sum_mul]
      rfl
    rw [e1]
    exact sum_mem fun PP hPP => comp_mem hc hN (hes PP hPP) (hx PP hPP)

end GlobalTheory.AdForm.HalfLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentHalfMemCompletedHomLatticeIffLocalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentHalf_mem_completedHomLattice_iff_local : ∀ (D : D7) (S T : HSp D), D.host.ccK = ⊤ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, (((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) := by
  first | exact @GlobalTheory.AdForm.HalfLat.half_mem_latO_iff | exact GlobalTheory.AdForm.HalfLat.half_mem_latO_iff | (intros; apply GlobalTheory.AdForm.HalfLat.half_mem_latO_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomAtIffLocPPerO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HomAtPer

theorem exists_den_away (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ z : 𝓞 D.host.E, z ∉ P.asIdeal ∧ ∀ t ∈ D.host.AA0, ∃ w : 𝓞 D.host.E, (w : D.host.E) = t * z := by
  haveI := P.isPrime
  have : Finite (𝓞 D.host.E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hl : (ringChar (𝓞 D.host.E ⧸ P.asIdeal)).Prime := CharP.char_is_prime (𝓞 D.host.E ⧸ P.asIdeal) _
  have hlP : ((ringChar (𝓞 D.host.E ⧸ P.asIdeal) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ _
  have h2 : ((D.host.QS : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    hP (by push_cast; exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_right _ h))
  have hq : ((D.host.q : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    hP (by push_cast; exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_left _ h))
  exact GlobalTheory.AAUnitAway.exists_den D P.asIdeal hl (UpperTheory.Ram.notMem_small_of_QS_notMem D.host hlP h2)
    (fun e => hq (e ▸ hlP)) hlP

theorem homAt_iff_locP_perO : ∀ (D : D7) (S T : HSp D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ x : Formalism.L2.Col.HomE D.host.E S.rank T.rank, x ∈ Formalism.L2.Col.homAt SS N N' ↔ ∀ P ∈ SS, x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D S T SS hSS N N' hN _hN' x
  constructor
  · intro hx P hP
    haveI := P.isPrime
    obtain ⟨gens, hgens⟩ := hN.1.fg
    have hden : ∀ g ∈ gens, ∃ s : 𝓞 D.host.E, s ∉ P.asIdeal ∧ s • x g ∈ N' := by
      intro g hg
      have hg' : g ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N :=
        ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul, ← hgens]; exact Submodule.subset_span hg⟩
      obtain ⟨s, hs, hsx⟩ := hx P hP g hg'
      exact ⟨s, hs, hsx⟩
    choose! sg hsg using hden
    set s : 𝓞 D.host.E := ∏ g ∈ gens, sg g with hs
    have hsP : s ∉ P.asIdeal := by
      rw [hs]
      intro hm
      obtain ⟨g, hg, hgP⟩ := Ideal.IsPrime.prod_mem_iff.1 hm
      exact (hsg g hg).1 hgP
    have hsx : s • x ∈ homO N N' := by
      intro y hy
      rw [← hgens] at hy
      induction hy using Submodule.span_induction with
      | mem g hg =>
        have e : (s • x) g = (∏ g' ∈ gens.erase g, sg g') • (sg g • x g) := by
          rw [LinearMap.smul_apply, smul_smul, hs, ← Finset.mul_prod_erase gens sg hg, mul_comm]
        rw [e]; exact N'.smul_mem _ (hsg g hg).2
      | zero => rw [map_zero]; exact N'.zero_mem
      | add y z _ _ h1 h2 => rw [map_add (f := _)]; exact N'.add_mem h1 h2
      | smul o y _ h => rw [LinearMap.map_smul_of_tower]; exact N'.smul_mem _ h
    exact ⟨s, hsP, Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, s • x, hsx, (one_smul _ _).symm⟩⟩
  · intro hx P hP y hy
    haveI := P.isPrime
    obtain ⟨z, hz, hden⟩ := exists_den_away D P (hSS P hP)
    obtain ⟨s, hs, hsx⟩ := hx P hP
    obtain ⟨t, ht, hty⟩ := hy
    have hper : ∀ w ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∀ v ∈ N, (z • w) v ∈ N' := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w h =>
        obtain ⟨r, hr, h0, hh0, rfl⟩ := h
        intro v hv
        obtain ⟨ρ, hρ⟩ := hden r hr
        have e : (z • r • h0) v = ρ • h0 v := by
          rw [LinearMap.smul_apply, LinearMap.smul_apply, ← algebraMap_smul D.host.E z, ← algebraMap_smul D.host.E ρ, smul_smul]
          congr 1
          change (z : D.host.E) * r = (ρ : D.host.E)
          rw [hρ, mul_comm]
        rw [e]; exact N'.smul_mem ρ (hh0 v hv)
      | zero => intro v _; rw [smul_zero, LinearMap.zero_apply]; exact N'.zero_mem
      | add w₁ w₂ _ _ h1 h2 => intro v hv; rw [smul_add, LinearMap.add_apply]; exact N'.add_mem (h1 v hv) (h2 v hv)
      | smul r w₁ _ h1 => intro v hv; rw [smul_comm, LinearMap.smul_apply]; exact N'.smul_mem r (h1 v hv)
    refine ⟨z * s * t, P.asIdeal.primeCompl.mul_mem (P.asIdeal.primeCompl.mul_mem hz hs) ht, ?_⟩
    have e : (z * s * t) • x y = (z • s • x) (t • y) := by
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.smul_apply, smul_smul, smul_smul]
      congr 1; ring
    rw [e]
    exact hper _ hsx _ hty

end GlobalTheory.HomAtPer
end
end
