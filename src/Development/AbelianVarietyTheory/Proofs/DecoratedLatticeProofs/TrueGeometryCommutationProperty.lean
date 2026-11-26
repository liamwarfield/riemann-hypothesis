module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadsRename
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.Rebase

section Core
open _root_.Formalism.L2.Col _root_.Formalism.L2.DIV GlobalTheory.Mem.Col2.ZeroMove

theorem exists_move {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) {n : ℕ} {ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 E))}
    (W : Finset (HeightOneSpectrum (𝓞 F))) (p0 p1 : DecoF E n ST SG Q)
    (hdeco : p1.deco = p0.deco) (hQ1 : ∀ P ∈ Q, P.under (𝓞 F) ∈ W)
    (hoff : ∀ P, P ∈ ST ∨ P ∈ SG → P.under (𝓞 F) ∉ W) (k g1 : GL (Fin n) (AfE F E))
    (hpt : IsPtOf hc k (extTo SQ p0)) (hg1 : IsPtOf hc g1 (extTo SQ p1)) :
    ∃ κ : GL (Fin n) (AfE F E), (∀ v ∉ W, bc (prV (E := E) v) κ = 1) ∧ IsPtOf hc (k * κ) (extTo SQ p1) := by
  have hN : (extTo SQ p1).deco.1.N = (extTo SQ p0).deco.1.N := by
    show p1.deco.1.N = p0.deco.1.N
    rw [hdeco]
  have hxU : k⁻¹ * g1 ∈ UPts hc.sig 1 (FiniteAdeleRing (𝓞 F) F) := mul_mem (inv_mem hpt.uni) hg1.uni
  have hxC : Formalism.L2.Herm.Carries (k⁻¹ * g1) (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) := by
    intro z
    have e1 := hpt.lat (((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) _) *ᵥ z)
    have e2 := hg1.lat (((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) _) *ᵥ z)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at e1
    rw [hN] at e2
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec, ← e2, e1]
  obtain ⟨κ, hκU, hκin, hκout⟩ := exists_splice hc.sig 1 W (k⁻¹ * g1) hxU
  have hκC : Formalism.L2.Herm.Carries κ (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) :=
    carries_of_local _ κ hxC fun v => if hv : v ∈ W then Or.inl (hκin v hv) else Or.inr (hκout v hv)
  have hof : ∀ P : HeightOneSpectrum (𝓞 E), (P ∈ ST ∨ P ∈ SG) → bc (prV (E := E) (P.under (𝓞 F))) κ = 1 :=
    fun P hP => hκout _ (hoff P hP)
  have hd' : (extTo SQ p1).deco = (extTo SQ p0).deco := hdeco
  refine ⟨κ, hκout, mul_mem hpt.uni hκU, ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P i j => ?_⟩
  · rw [hN]
    exact GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm.carries_mul hpt.lat hκC
  · rw [adAt_pullV_mul P.1 k (hof P.1 (Or.inl P.2)), hd']
    exact hpt.f P x (by rw [← hN]; exact hx) i hi
  · rw [adAt_pullV_mul w.1 k (hof w.1 (Or.inr w.2)), hd']
    exact hpt.be w x (by rw [← hN]; exact hx) i
  · by_cases hv : P.1.under (𝓞 F) ∈ W
    · rw [adAt_mul_congr P.1 k (hκin _ hv) i j, mul_inv_cancel_left]
      exact hg1.fr P i j
    · have hQa : P.1 ∉ Q := fun h => hv (hQ1 _ h)
      rw [adAt_mul_of_one P.1 k (hκout _ hv) i j, hpt.fr P i j, extTo_fr, extTo_fr,
        ptFr_eq p0 p1 hdeco.symm hQa hQa]

end Core

def reindex {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl cl' : Type}
    {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) (e : cl' → cl) (he : Function.Bijective e) :
    LevelChart D T bad i hi (fun c => stab (e c)) (fun c => lat (e c)) where
  lev := K.lev
  y c := K.y (e c)
  y_bij := K.y_bij.comp he
  y_lat c := K.y_lat (e c)
  stabI c := K.stabI (e c)
  stabI_inj c := K.stabI_inj (e c)
  stabI_range c := K.stabI_range (e c)

theorem reads_rename {B : Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word} {a : I.ι} {i : ℕ} {C C₀ : Type}
    {chOf₀ : (I.stp u a i).Cl → C₀} {Lb : C₀ → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U : C₀ → Subgroup (TC.GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a i).Cl → TC.GA B (B.R.N i)}
    {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k : C₀ → TC.GA B (B.R.N i)}
    (h : I.Reads u a i chOf₀ Lb U chi y st k) (chOf : (I.stp u a i).Cl → C) (φ : C → C₀) (hφ : ∀ c, chOf₀ c = φ (chOf c))
    (hinj : Function.Injective φ) (hon : Function.Surjective chOf) :
    I.Reads u a i chOf (fun β => Lb (φ β)) (fun β => U (φ β)) (fun β => chi (φ β)) y st (fun β => k (φ β)) := by
  refine ⟨?_, hon, fun β => h.lb (φ β), fun β => h.k_std (φ β), fun β => h.k_off (φ β),
    fun β => h.k_T (φ β), ?_, ?_, ?_, h.stab⟩
  · intro c c'
    simpa only [hφ, hinj.eq_iff] using h.key c c'
  · intro c
    simpa only [hφ] using h.pt c
  · intro c x q
    simpa only [hφ] using h.lev c x q
  · intro c
    have key : ∀ γ, chOf₀ c = γ → ∀ (x : U γ) (κ : (I.stp u a i).G c.1), (I.stp u a i).gam c.1 κ = 1 →
        TC.PtOf (y c * x.1 * k γ) ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1 →
        ((chi γ x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ : B.LLˣ) : B.LL) := by
      rintro _ rfl
      exact h.chr c
    exact key _ (hφ c)

variable {B : Base} {X : PreX B.toPre}


set_option maxHeartbeats 2000000 in
theorem exists_charts (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (i : ℕ) (hi : i ≤ B.R.m) (h1 : 1 ≤ i) (h2 : i < B.R.m) {C : Type} (chOf : (I.stp u a i).Cl → C)
    (key : ∀ c c', chOf c = chOf c' ↔ c.1 = c'.1 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn ((I.stp u a i).rep c'))
    (onto : Function.Surjective chOf) (k : C → TC.GA B (B.R.N i)) (hk : GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k) :
    ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
      (K : ∀ β : C, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))),
      I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
        (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
      (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) ∧
      ∀ v ∈ bad, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v := by
  let Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) := (I.Q a).image (fun P => P.under (𝓞 B.host.F))
  have hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v := fun v => Finset.mem_image
  have key₀ : ∀ c c', GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c' ↔ chOf c = chOf c' :=
    fun c c' => by
      rw [key]
      exact Subtype.ext_iff.trans Prod.ext_iff
  let φ : C → GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i := fun β => GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i (Function.surjInv onto β)
  let ψ : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → C := fun γ => chOf γ.2.choose
  have hφ : ∀ c, GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = φ (chOf c) := fun c =>
    (key₀ _ _).2 (Function.surjInv_eq onto _).symm
  have hψ : ∀ β, ψ (φ β) = β := fun β => by
    refine Eq.trans ((key₀ _ _).1 ?_) (Function.surjInv_eq onto β)
    exact Subtype.ext (φ β).2.choose_spec
  have hinj : Function.Injective φ := Function.LeftInverse.injective hψ
  obtain ⟨K, hK, hfin⟩ := GlobalTheory.Mem.Col2.ChExM.exists_charts I hI hP l Z u a Q i hi h1 h2 hQ (fun γ => k (ψ γ))
    ⟨fun γ => hk.std _, fun γ => hk.off _, fun γ => hk.T _⟩
  let e : ∀ β : C, {c // chOf c = β} → {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = φ β} :=
    fun β c => ⟨c.1, (hφ c.1).trans (congrArg φ c.2)⟩
  have he : ∀ β, Function.Bijective (e β) := fun β =>
    ⟨fun c c' h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h', fun c => ⟨⟨c.1, hinj ((hφ c.1).symm.trans c.2)⟩, rfl⟩⟩
  refine ⟨badQ (I.rec7 l Z) Q, fun β => reindex (K (φ β)) (e β) (he β), ?_, fun β => hfin (φ β), fun v hv => hv.imp id (hQ v).1⟩
  have h := reads_rename hK chOf φ hφ hinj onto
  have hy : ∀ c γ (hc : GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = γ),
      ((K γ).y ⟨c, hc⟩).1 = ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1 := by
    rintro c _ rfl
    rfl
  have hs : ∀ c γ (hc : GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = γ) s,
      ((K γ).stabI ⟨c, hc⟩ s).1 = ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1 := by
    rintro c _ rfl s
    rfl
  have e1 : (fun β => k (ψ (φ β))) = k := funext fun β => congrArg k (hψ β)
  rw [e1, ← funext fun c => hy c _ (hφ c), ← funext fun c => funext fun s => hs c _ (hφ c) s] at h
  exact h

def StepOk {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (i : ℕ)
    (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
    (K : ∀ (hi : i ≤ B.R.m) (β : Ch i), LevelChart (I.rec7 l Z) (B.T u) bad i hi
      (fun c : {c // A.chOf i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)))
    (k : Ch i → TC.GA B (B.R.N i)) (kA : Ch i → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (xr : Ch i → (AE (I.rec7 l Z))ˣ)
    (p0 : Ch i → PtAt B.R I.sel (I.tup a) (I.cst a) u i) (U : Ch i → Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)))
    (chi : ∀ β, U β →* ℂˣ) (h : ∀ β : Ch i, {c // A.chOf i c = β} → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) : Prop :=
  ∀ hi : i ≤ B.R.m, I.Reads u a i (A.chOf i) (fun β => (K hi β).lev.Lb) (fun β => (K hi β).lev.U) (fun β => (K hi β).lev.chi)
      (fun c => ((K hi (A.chOf i c)).y ⟨c, rfl⟩).1) (fun c s => ((K hi (A.chOf i c)).stabI ⟨c, rfl⟩ s).1) k ∧
    (∀ β, kA β ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (kA β) = (k β).1 ∧ IsDetRoot _ (kA β) (xr β)) ∧
    (∀ β, TC.PtOf (k β) (extTo I.SQ (p0 β).1.1) ∧ (p0 β).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) ∧
    (∀ c, cosetIn ((I.stp u a i).rep c) = cosetIn (p0 (A.chOf i c))) ∧
    (∀ β g, g ∈ U β ↔ g ∈ GfC _ ∧ ∃ κ : (K hi β).lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g) ∧
    (∀ β (g : U β) (κ : (K hi β).lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 → chi β g = (K hi β).lev.chi κ) ∧
    (∀ β c, h β c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (h β c) = ((K hi β).y c).1.1) ∧
    (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K hi β).lev.chi κ ^ n = 1) ∧ ∀ v ∈ bad, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v

attribute [local instance] GlobalTheory.Mem.Col2.starE


set_option maxHeartbeats 2000000 in
theorem exists_step {I : TC B X} (hI : I.Ok) (hP : TC.Pins B X) {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hm : i + 1 = B.R.m)
    (q : Ch i → Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i) (κ : Ch i → TC.GA B (B.R.N i))
    (hoff : ∀ β v, ¬ I.UnderQ a v → bc (prV (E := B.host.E) v) (κ β) = 1)
    (hpt : ∀ β, TC.PtOf (A.kb i β * κ β) (extTo I.SQ (q β)))
    (hN : ∀ β, (q β).deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) :
    ∃ bad K kA xr p0 U chi h, StepOk A i bad K (fun β => A.kb i β * κ β) kA xr p0 U chi h ∧ ∀ β, (p0 β).1.1 = q β := by
  have hi : i ≤ B.R.m := by omega
  have h2m := B.R.two_le_m
  have hR₀ := hA.reads i hi
  have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
  have hk : GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i (fun β => A.kb i β * κ β) := by
    refine ⟨fun β => ?_, fun β v h1 h2 h3 => ?_, fun β P r j hr => ?_⟩
    · obtain ⟨p, hp, hpN⟩ := hR₀.k_std β
      refine ⟨p, ⟨(hpt β).uni, ?_, fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _),
        fun P => absurd P.2 (Finset.notMem_empty _)⟩, hpN⟩
      have e := (hpt β).lat
      rw [extTo_deco, hN] at e
      rw [hpN]
      exact e
    · rw [map_mul, hR₀.k_off β v h1 h2 h3, hoff β v h2, mul_one]
    · have e : bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (A.kb i β * κ β)⁻¹ =
          bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (A.kb i β)⁻¹ := by
        rw [map_inv, map_mul, hoff β _ (GlobalTheory.Mem.Col2.ZeroMove.not_underQ I hI u a (Or.inl P.2)), mul_one, map_inv]
      have e2 := GlobalTheory.Mem.Col2.ZeroMove.adAt_entry_of_bc (F := B.host.F) (E := B.host.E) P.1 e r j
      exact e2 ▸ hR₀.k_T β P r j hr
  obtain ⟨bad, K, hR, hfin, hbad⟩ := exists_charts I hI hP l Z u a i hi (by omega) (by omega) (A.chOf i) hR₀.key hR₀.onto _ hk
  have hq : ∀ β, TC.PtOf (A.kb i β * κ β) (q β) := fun β => IsPtOf.of_extTo (I.Q_subset_SQ a) hd (hpt β)
  have hone : ∀ β, ∀ P ∈ I.SQ, P ∉ I.Q a → (A.kb i β * κ β).1.map (adAt B.host.F P) = 1 := by
    intro β P hP' hPQ
    have hPG : P ∉ (B.primes X).vGs := Finset.disjoint_right.1 (LevTwist.levOk_twists B X I hI).2.1 hP'
    have hfr : ptFr (q β) P = 1 := by
      unfold ptFr
      rw [dite_eq_right hPG, dite_eq_right hPQ, hN]
      unfold GlobalTheory.Mem.Col2.latFr
      exact if_pos rfl
    refine Matrix.ext fun r s => ?_
    have e := (hpt β).fr ⟨P, hP'⟩ r s
    rw [extTo_fr, hfr] at e
    refine e.trans ?_
    show algebraMap _ _ ((Pi.single s 1 : Fin (B.R.N i) → B.host.E) r) = _
    rw [Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  choose kA hkA using fun β => GlobalTheory.T.exists_adelicUnitaryLift_of_chartBasePoint I hI hP l Z i hi _ (hR.k_std β)
  choose xr hxr using fun β => GlobalTheory.RecDict.exists_isDetRoot (I.rec7 l Z) _ (kA β)
  choose b0 p0 hp1 hp2 hp3 using fun β => GlobalTheory.KxPoint.pointOf_base I hI hP u a i hi _ _ _ _ _ _ _ hR β ⟨q β, hq β⟩ (hone β)
  choose U chi h hU hchi hh using fun β => GlobalTheory.T.chartLevelCharacterReps_on_adelicUnitaryPoints I l Z i hi (K β)
  refine ⟨bad, fun _ => K, kA, xr, p0, U, chi, h, fun _ => ⟨hR, fun β => ⟨(hkA β).1, (hkA β).2, hxr β⟩, fun β => ⟨hp1 β, hp2 β⟩,
    fun c => (hp3 _ c rfl).2, hU, hchi, hh, hfin, hbad⟩, fun β => ?_⟩
  exact GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique _ _ _ _ (IsPtOf.of_extTo (I.Q_subset_SQ a) hd (hp1 β)) (hq β)


set_option maxHeartbeats 2000000 in
theorem exists_moved {I : TC B X} (hI : I.Ok) (hP : TC.Pins B X) {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (hA : A.Is)
    (q : ∀ i, Ch i → Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i) (κ : ∀ i, Ch i → TC.GA B (B.R.N i))
    (hoff : ∀ i, i + 1 = B.R.m → ∀ β v, ¬ I.UnderQ a v → bc (prV (E := B.host.E) v) (κ i β) = 1)
    (hpt : ∀ i, i + 1 = B.R.m → ∀ β, TC.PtOf (A.kb i β * κ i β) (extTo I.SQ (q i β)))
    (hN : ∀ i, i + 1 = B.R.m → ∀ β, (q i β).deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) :
    ∃ A' : TwDat I l Z u a Ch, A'.Is ∧ A'.chr = A.chr ∧ A'.b0 = A.b0 ∧ (∀ i, i + 1 ≠ B.R.m → A'.kb i = A.kb i ∧ A'.p0 i = A.p0 i) ∧
      ∀ i, i + 1 = B.R.m → ∀ β, A'.kb i β = A.kb i β * κ i β ∧ (A'.p0 i β).1.1 = q i β ∧
        cosetIn (A'.p0 i β) = cosetIn (A.p0 i β) := by
  have H : ∀ i, ∃ bad K k kA xr p0 U chi h, StepOk A i bad K k kA xr p0 U chi h ∧ (i + 1 ≠ B.R.m → k = A.kb i ∧ p0 = A.p0 i) ∧
      (i + 1 = B.R.m → ∀ β, k β = A.kb i β * κ i β ∧ (p0 β).1.1 = q i β) := by
    intro i
    by_cases hm : i + 1 = B.R.m
    · obtain ⟨bad, K, kA, xr, p0, U, chi, h, h1, h2⟩ := exists_step hI hP A hA i hm (q i) (κ i) (hoff i hm) (hpt i hm) (hN i hm)
      exact ⟨bad, K, _, kA, xr, p0, U, chi, h, h1, fun h' => absurd hm h', fun _ β => ⟨rfl, h2 β⟩⟩
    · exact ⟨A.bad i, A.K i, A.kb i, A.kA i, A.xr i, A.p0 i, A.U i, A.chi i, A.h i,
        fun hi => ⟨hA.reads i hi, hA.kA i hi, hA.base i hi, fun c => (hA.rep i hi c).2, hA.U i hi, hA.chi i hi, hA.h i hi,
          hA.fin i hi, hA.bad_le i hi⟩, fun _ => ⟨rfl, rfl⟩, fun h' => absurd h' hm⟩
  choose bad K k kA xr p0 U chi h hS hne heq using H
  refine ⟨⟨bad, A.chOf, K, k, kA, xr, A.b0, p0, U, chi, h, A.chr, A.e⟩,
    ⟨fun i hi => (hS i hi).1, fun β => ?_, fun i hi => (hS i hi).2.1, fun i hi => (hS i hi).2.2.1,
      fun i hi c => ⟨(hA.rep i hi c).1, (hS i hi).2.2.2.1 c⟩, fun i hi => (hS i hi).2.2.2.2.1, fun i hi => (hS i hi).2.2.2.2.2.1,
      fun i hi => (hS i hi).2.2.2.2.2.2.1, hA.chr, hA.idem, fun i hi => (hS i hi).2.2.2.2.2.2.2.1,
      fun i hi => (hS i hi).2.2.2.2.2.2.2.2⟩, rfl, rfl, hne, fun i hm β => ⟨(heq i hm β).1, (heq i hm β).2, ?_⟩⟩
  · show I.TopPt l Z u a (k B.R.m β)
    rw [(hne B.R.m (by omega)).1]
    exact hA.top β
  · have hi : i ≤ B.R.m := by omega
    obtain ⟨c, rfl⟩ := (hA.reads i hi).onto β
    exact ((hS i hi).2.2.2.1 c).symm.trans (hA.rep i hi c).2


open _root_.Formalism.L2.Col in
theorem exists_frames {I : TC B X} (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ}
    (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i) (k : TC.GA B (B.R.N i)) (hk : TC.PtOf k (extTo I.SQ p))
    (hN : p.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i))
    (r : I.Q a → (Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)))
    (hr : ∀ P, r P ∈ GLint B.fields.E (B.R.N i) P.1) :
    ∃ (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i) (κ : TC.GA B (B.R.N i)), q.deco = p.deco ∧ (∀ P, q.fr P = r P) ∧
      (∀ v, ¬ I.UnderQ a v → bc (prV (E := B.host.E) v) κ = 1) ∧ TC.PtOf (k * κ) (extTo I.SQ q) := by
  let q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i := ⟨(p.deco, r), fun P x => by
    show r P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N ↔ _
    rw [hN]
    exact hr P x⟩
  let Q : Finset (HeightOneSpectrum (𝓞 B.host.F)) := (I.Q a).image (fun P => P.under (𝓞 B.host.F))
  have hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v := fun v => Finset.mem_image
  obtain ⟨g1, hg1⟩ := PtTwist.exists_ptOf_twists I hI u _ (extTo I.SQ q)
  obtain ⟨κ, h1, h2⟩ := exists_move B.sp.cm Q p q rfl (fun P h => (hQ _).2 ⟨P, h, rfl⟩)
    (fun P hP hv => GlobalTheory.Mem.Col2.ZeroMove.not_underQ I hI u a hP ((hQ _).1 hv)) k g1 hk hg1
  exact ⟨q, κ, rfl, fun _ => rfl, fun v hv => h1 v fun h => hv ((hQ v).1 h), h2⟩


open _root_.Formalism.L2.Col in
theorem repY_cong {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Formalism.L2.DIV.Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (h : j + 1 = R.m)
    (p p' : PtAt R sel mu cst u j) (hc : cosetIn p' = cosetIn p) (P : rowSG Pr sel mu) :
    ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ •
      ((frsF sel mu p'.1.1 P).symm (repY p'.1.2) - (frsF sel mu p.1.1 P).symm (repY p.1.2)) ∈ stdAt X.E (R.N j) P.1 := by
  have h1 : (frsF sel mu p'.1.1 P).symm (repY p'.1.2) ∈ cosetIn p' P :=
    ⟨_, p'.repY_mem h, by rw [sub_self, smul_zero]; exact zero_mem _⟩
  rw [hc] at h1
  obtain ⟨y, hy, h2⟩ := h1
  obtain ⟨y₀, -, hY⟩ := p.mem_ybSet h
  have h3 := p.repY_mem h
  have hy' : y - y₀ ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
    rw [hY] at hy
    exact hy
  have h3' : repY p.1.2 - y₀ ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
    generalize repY p.1.2 = z at h3
    rw [hY] at h3
    exact h3
  have h4 := (mem_locLat _ _ _ _).1 (sub_mem hy' h3') P
  rw [sub_sub_sub_cancel_right] at h4
  have h5 : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ))) =
      (qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M) := by
    split_ifs <;> simp
  rw [h5] at h4
  have h6 : (frsF sel mu p.1.1 P).symm (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (y - repY p.1.2)) ∈
      stdAt X.E (R.N j) P.1 := by
    refine (isFr_ptFr p.1.1 P.1 _).1 ?_
    rw [← frsF_eq_ptFr, LinearEquiv.apply_symm_apply]
    exact h4
  have h7 := add_mem h2 h6
  rwa [map_smul, map_sub, ← smul_add, sub_add_sub_cancel] at h7

end GlobalTheory.AdForm.Rebase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiCpl1EqZeroOfFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FullOfSpanEqTop
namespace GlobalTheory.FullLatticeOfSpan

open NumberField

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (N : Submodule (𝓞 E) V) {x : V}
    (hx : x ∈ Submodule.span E (N : Set V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hay
    · rw [mul_smul]; exact N.smul_mem _ hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hsE : algebraMap (𝓞 E) E s ≠ 0 := by
      intro h
      exact hs0 (IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero]))
    refine ⟨a * s, mul_ne_zero ha hs0, ?_⟩
    have : (a * s) • ((algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s) • y) = r • (a • y) := by
      rw [← algebraMap_smul E (a * s), ← algebraMap_smul E r, ← algebraMap_smul E a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact N.smul_mem _ hay

theorem exists_nat_dvd {E : Type} [Field E] [NumberField E] (d : 𝓞 E) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ d ∣ (m : 𝓞 E) := by
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  · exact Ideal.mem_span_singleton.mp (Ideal.absNorm_mem _)

theorem full_of_span_eq_top : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (N : Submodule (NumberField.RingOfIntegers E) (Formalism.L2.Col.Sp E n)),
    Submodule.span E (↑N : Set (Formalism.L2.Col.Sp E n)) = ⊤ → GlobalTheory.ThetaMove.Full N := by
  intro E _ _ n N hN x
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem N (x := x) (by rw [hN]; trivial)
  obtain ⟨m, hm, c, hc⟩ := exists_nat_dvd d hd
  refine ⟨m, hm, ?_⟩
  rw [hc, mul_comm, mul_smul]
  exact N.smul_mem _ hdx

end GlobalTheory.FullLatticeOfSpan
end

open NumberField IsDedekindDomain Matrix ValuativeRel Formalism.L2.Col
open scoped Classical

noncomputable section

namespace GlobalTheory.CplDead

open Formalism.HermitianLatticesTheory GlobalTheory.ThetaMove

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem full_finset_inf {W ι : Type} [AddCommGroup W] [Module (𝓞 E) W] (S : Finset ι) (M : ι → Submodule (𝓞 E) W)
    (hM : ∀ i, Full (M i)) : Full (S.inf M) := by
  induction S using Finset.induction_on with
  | empty => intro x; exact ⟨1, one_pos, by simp⟩
  | insert i S hi ih => rw [Finset.inf_insert]; exact (hM i).inf ih

theorem exists_approx_family {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (S : Finset (HeightOneSpectrum (𝓞 E)))
    (M : HeightOneSpectrum (𝓞 E) → Submodule (𝓞 E) W) (hM : ∀ P, Full (M P)) (x : HeightOneSpectrum (𝓞 E) → W) :
    ∃ t : W, ∀ P ∈ S, t - x P ∈ localization₂ P.asIdeal (M P) := by
  have h := fun P => (full_finset_inf S M hM).approx {P} (x P)
  choose t h1 h2 using h
  refine ⟨∑ P ∈ S, t P, fun P hP => localization_mono P (Finset.inf_le hP) ?_⟩
  rw [← Finset.add_sum_erase S t hP, add_sub_right_comm]
  refine Submodule.add_mem _ (h1 P P (Finset.mem_singleton_self P)) (Submodule.sum_mem _ fun Q hQ => h2 Q P ?_)
  rw [Finset.mem_singleton]
  exact (Finset.ne_of_mem_erase hQ).symm

theorem full_of_span {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (hN : Submodule.span E (N : Set (Sp E n)) = ⊤) : Full N := by
  first
  | exact @_root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top
  | exact _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top
  | (apply _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FullLatticeOfSpan.full_of_span_eq_top ..)

theorem full_stdLat (n : ℕ) : Full (stdLat E n) := by
  refine full_of_span _ (top_le_iff.1 fun x _ => ?_)
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span fun j _ => ?_)
  by_cases h : i = j
  · simp only [if_pos h]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  · simp only [if_neg h]; exact Submodule.zero_mem _

theorem intAt_of_mem_stdAt {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {x : Sp E n} (hx : x ∈ stdAt E n P) (i : Fin n) :
    IntAt P (x i) := by
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i (Set.mem_univ i))
  exact ⟨r, s, hs, by rw [hr]; rfl⟩

variable {a b : ℕ}

def homInto (S₀ : Set (Sp E a)) (g : Sp E b →ₗ[E] Sp E b) (N : Submodule (𝓞 E) (Sp E b)) : Submodule (𝓞 E) (HomE E a b) where
  carrier := {z | ∀ y ∈ S₀, g (z y) ∈ N}
  zero_mem' := fun y _ => by simp
  add_mem' := fun {z z'} hz hz' y hy => by
    rw [LinearMap.add_apply, map_add (f := _)]; exact N.add_mem (hz y hy) (hz' y hy)
  smul_mem' := fun c z hz y hy => by
    rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower]; exact N.smul_mem _ (hz y hy)

theorem full_homInto (S₀ : Finset (Sp E a)) (g : Sp E b →ₗ[E] Sp E b) {N : Submodule (𝓞 E) (Sp E b)} (hN : Full N) :
    Full (homInto (S₀ : Set (Sp E a)) g N) := by
  intro z
  choose n hn hz using fun y => hN (g (z y))
  refine ⟨∏ y ∈ S₀, n y, Finset.prod_pos fun y _ => hn y, fun y hy => ?_⟩
  rw [LinearMap.smul_apply, LinearMap.map_smul_of_tower, ← Finset.prod_erase_mul S₀ n hy, Nat.cast_mul, mul_smul]
  exact N.smul_mem _ (hz y)

theorem apply_mem_of_mem_locP {S₀ : Set (Sp E a)} {g : Sp E b →ₗ[E] Sp E b} {N : Submodule (𝓞 E) (Sp E b)}
    {P : HeightOneSpectrum (𝓞 E)} {z : HomE E a b} (hz : z ∈ localization₂ P.asIdeal (homInto S₀ g N)) {y : Sp E a}
    (hy : y ∈ localization₂ P.asIdeal (Submodule.span (𝓞 E) S₀)) : g (z y) ∈ localization₂ P.asIdeal N := by
  obtain ⟨s, hs, hz⟩ := hz
  obtain ⟨t, ht, hy⟩ := hy
  have h : ∀ w ∈ Submodule.span (𝓞 E) S₀, g ((s • z) w) ∈ N := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact hz w hw
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _), map_add (f := _)]; exact N.add_mem hu hv
    | smul c u _ hu => rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower]; exact N.smul_mem _ hu
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  have := h _ hy
  rwa [LinearMap.smul_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
    smul_smul] at this

variable [StarRing E]

theorem phiT_add (K : Type) [Field K] {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E a ST SG)
    {d' : Deco E b ST SG'} (hd' : d'.Ok) (x z : HomE E a b)
    (hz : ∀ P : ST, ∀ y ∈ d.at P.1, ((qOf P.1 : E))⁻¹ • z y ∈ d'.at P.1) : phiT K d d' (x + z) = phiT K d d' x := by
  have key : ∀ x z : HomE E a b, (∀ P : ST, ∀ y ∈ d.at P.1, ((qOf P.1 : E))⁻¹ • z y ∈ d'.at P.1) →
      (∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y) →
      ∀ P : ST, ∀ y ∈ d.at P.1, (x + z) y ∈ d'.at P.1 ∧ d'.f P ((x + z) y) = d.f P y := by
    intro x z hz hx P y hy
    have hq : (qOf P.1 : E) ≠ 0 := by
      have : qOf P.1 ≠ 0 := by rw [qOf, Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot
      exact_mod_cast this
    have e : z y = (qOf P.1 : 𝓞 E) • ((qOf P.1 : E))⁻¹ • z y := by
      rw [← algebraMap_smul E (qOf P.1 : 𝓞 E), map_natCast, smul_smul, mul_inv_cancel₀ hq, one_smul]
    have h1 : z y ∈ d'.at P.1 := by rw [e]; exact Submodule.smul_mem _ _ (hz P y hy)
    have h2 : d'.f P (z y) = 0 := by
      rw [e, hd'.f_smul P _ _ (hz P y hy), Ideal.Quotient.eq_zero_iff_mem.2
        (show (qOf P.1 : 𝓞 E) ∈ P.1.asIdeal from Ideal.absNorm_mem _), zero_mul]
    rw [LinearMap.add_apply]
    exact ⟨Submodule.add_mem _ (hx P y hy).1 h1, by rw [hd'.f_add P _ (hx P y hy).1 _ h1, h2, add_zero, (hx P y hy).2]⟩
  unfold phiT
  refine if_congr ⟨fun h => ?_, key x z hz⟩ rfl rfl
  have := key (x + z) (-z) (fun P y hy => by
    rw [LinearMap.neg_apply, smul_neg]; exact Submodule.neg_mem _ (hz P y hy)) h
  rwa [add_neg_cancel_right] at this

theorem exists_transport (K : Type) [Field K] {ST SG SG' SB : Finset (HeightOneSpectrum (𝓞 E))} (hdis : Disjoint ST SB)
    {d : Deco E a ST SG} (hd : d.Ok) {d' : Deco E b ST SG'} (hd' : d'.Ok) (f₀ : Frs E a SB) (f f' : Frs E b SB)
    (c : SB → E) (x : HomE E a b) :
    ∃ x' : HomE E a b, phiT K d d' x' = phiT K d d' x ∧
      ∀ (P : SB) s l, IntAt P.1 (c P * (inFr (f₀ P) (f P) x' - inFr (f₀ P) (f' P) x) (Pi.single s 1) l) := by
  obtain ⟨S₀, hS₀⟩ := hd.lat.fg
  obtain ⟨S₁, hS₁⟩ := hd'.lat.fg
  have hone : Full (1 : Submodule (𝓞 E) E) := by
    intro x
    obtain ⟨n, hn, hnx⟩ := full_stdLat (E := E) 1 (fun _ => x)
    refine ⟨n, hn, ?_⟩
    simpa [stdLat, Submodule.mem_pi] using hnx (0 : Fin 1) (Set.mem_univ _)
  have hfull : Full d'.N := by
    let M : Sp E b → Submodule (𝓞 E) (Sp E b) := fun y =>
      (1 : Submodule (𝓞 E) E).comap ((hStd E b y).restrictScalars (𝓞 E))
    have hM : ∀ y, Full (M y) := by
      intro y x
      obtain ⟨n, hn, hx⟩ := hone (hStd E b y x)
      refine ⟨n, hn, ?_⟩
      simpa [M] using hx
    have hle : S₁.inf M ≤ d'.N := by
      intro x hx
      rw [← hd'.uni]
      simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
        LinearMap.restrictScalars_apply]
      intro y hy
      rw [← hS₁] at hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact (show S₁.inf M ≤ M y from Finset.inf_le hy) hx
      | zero => simp
      | add y z hy hz ihy ihz => simpa using Submodule.add_mem (1 : Submodule (𝓞 E) E) ihy ihz
      | smul r y hy ih =>
        let r' : 𝓞 E := ⟨star (r : E), r.isIntegral_coe.map (starRingEnd E).toIntAlgHom⟩
        rw [← algebraMap_smul E r y, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
        have hr := (1 : Submodule (𝓞 E) E).smul_mem r' ih
        change star (r : E) * hStd E b y x ∈ (1 : Submodule (𝓞 E) E) at hr
        simpa [starRingEnd_apply, smul_eq_mul] using hr
    intro x
    obtain ⟨n, hn, hx⟩ := full_finset_inf S₁ M hM x
    exact ⟨n, hn, hle hx⟩
  obtain ⟨t, ht⟩ := exists_approx_family (W := HomE E a b) (ST ∪ SB)
    (fun P => if h : P ∈ SB then
        homInto ((Finset.univ.image fun s : Fin a => f₀ ⟨P, h⟩ (Pi.single s 1) : Finset (Sp E a)) : Set (Sp E a))
          (c ⟨P, h⟩ • (f ⟨P, h⟩).symm.toLinearMap) (stdLat E b)
      else homInto (S₀ : Set (Sp E a)) (((qOf P : E))⁻¹ • LinearMap.id) d'.N)
    (fun P => by
      by_cases h : P ∈ SB
      · simp only [dif_pos h]; exact full_homInto _ _ (full_stdLat b)
      · simp only [dif_neg h]; exact full_homInto _ _ hfull)
    (fun P => if h : P ∈ SB then (f ⟨P, h⟩).toLinearMap ∘ₗ (f' ⟨P, h⟩).symm.toLinearMap ∘ₗ x else x)
  refine ⟨t, ?_, fun P s l => ?_⟩
  · rw [← add_sub_cancel x t]
    refine phiT_add K d hd' x _ fun P y hy => ?_
    have h : P.1 ∉ SB := Finset.disjoint_left.1 hdis P.2
    have h1 := ht P.1 (Finset.mem_union_left _ P.2)
    simp only [dif_neg h] at h1
    exact apply_mem_of_mem_locP h1 (by rw [hS₀]; exact hy)
  · have h1 := ht P.1 (Finset.mem_union_right _ P.2)
    simp only [dif_pos P.2] at h1
    have h2 := apply_mem_of_mem_locP h1 (y := f₀ P (Pi.single s 1))
      (mem_localization_of_mem _ (Submodule.subset_span (by simp)))
    have h3 := intAt_of_mem_stdAt h2 l
    convert h3 using 1
    simp [inFr]

end Gen

theorem xiCpl1_eq_zero_of_frames : ∀ {X : Fields} {Pr : Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Formalism.L2.DIV.Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), L.Ok Ch sel mu cst G m2 → ∀ (u : Pr.Word), Disjoint (Pr.vT u) (rowSG Pr sel mu) → ∀ (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p p' : ChPt (R := R) sel mu u (m2 + 1)) (Y Y' : Set (Sp X.E (R.N (m2 + 1)))), p'.deco = p.deco → (∀ P : rowSG Pr sel mu, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • ((frsF sel mu p' P).symm (repY Y') - (frsF sel mu p P).symm (repY Y)) ∈ stdAt X.E (R.N (m2 + 1)) P.1) → (∀ x, XiCpl1 Ch sel mu cst L m2 al p₀ p Y x = 0) → ∀ x, XiCpl1 Ch sel mu cst L m2 al p₀ p' Y' x = 0 := by
  intro X Pr R Ch sel S mu cst L G m2 hL u hdis al p₀ p p' Y Y' hdeco hY h0 x
  obtain ⟨x', h1, h2⟩ := exists_transport X.K hdis p₀.deco.2 p.deco.2 (frsF sel mu p₀) (frsF sel mu p) (frsF sel mu p')
    (fun P => ((qOf P.1 : X.E) ^ cst.B)⁻¹) x
  rw [← h0 x']
  unfold XiCpl1
  rw [hdeco, h1]
  congr 1
  refine Finset.prod_congr rfl fun P _ => ?_
  have e1 := hL.psiInvX al P (inFr (frsF sel mu p₀ P) (frsF sel mu p' P) x) _ ((frsF sel mu p P).symm (repY Y)) (h2 P)
  have e2 := hL.psiInv al P (inFr (frsF sel mu p₀ P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))
    ((frsF sel mu p' P).symm (repY Y') - (frsF sel mu p P).symm (repY Y)) (fun i => intAt_of_mem_stdAt (hY P) i)
  rw [add_sub_cancel] at e1 e2
  rw [e1, e2]

end GlobalTheory.CplDead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRatOfSameOrb
open NumberField IsDedekindDomain Matrix ValuativeRel Formalism.L2.Col
open scoped Classical

namespace GlobalTheory.QPl.RatOrb
open GlobalTheory.StepData GlobalTheory.SplitWeil GlobalTheory.TwBridge.Lev GlobalTheory.TwBridge.LevOrb

theorem image_val_mem_nhds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {B : Type} [Fintype B] [DecidableEq B] {S : Set (GL B k)} (hS : IsOpen S) {h : GL B k} (hh : h ∈ S) :
    Units.val '' S ∈ nhds h.val := by
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hS
  have hd : h.val.det ≠ 0 := h.det_ne_zero
  have hc : ContinuousAt (Inv.inv : Matrix B B k → Matrix B B k) h.val := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  have hG : ContinuousAt (fun N : Matrix B B k => (N, MulOpposite.op N⁻¹)) h.val :=
    continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp hc)
  have key : ∀ u : GL B k, Units.embedProduct _ u = (u.val, MulOpposite.op u.val⁻¹) := fun u => by
    rw [Units.embedProduct_apply, Matrix.coe_units_inv]
  have h1 := hG.preimage_mem_nhds (hW.mem_nhds (by rw [← key]; exact hh))
  have h2 : {N : Matrix B B k | N.det ≠ 0} ∈ nhds h.val :=
    (isOpen_ne.preimage (continuous_id.matrix_det)).mem_nhds hd
  filter_upwards [h1, h2] with N hN1 hN2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero N hN2, ?_, rfl⟩
  rw [Set.mem_preimage, key]
  exact hN1

theorem exists_rat_of_sameOrb : ∀ {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P (qOf P) ι ϖ → ∀ {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (e : A ≃ Fin n) (Jl : Subgroup (GL (A ⊕ Fin 0) k)), IsOpen (Jl : Set (GL (A ⊕ Fin 0) k)) → Jl ≤ GlobalTheory.SplitWeil.KO k (A ⊕ Fin 0) → ∀ (M : ℕ) (c : (A → k) ⧸ GlobalTheory.StepData.box A (ϖ ^ M)) (y₀ : Sp E n), GlobalTheory.QPl.SameOrb Jl (GlobalTheory.StepData.box A (ϖ ^ M)) c (Submodule.Quotient.mk fun a => ι (y₀ (e a))) → ∃ r ∈ GLint E n P, ∃ g ∈ Jl, g.val.toBlocks₁₁ = GlobalTheory.SymBridge.toLoc ι e e r.toLinearMap ∧ ∀ y : Sp E n, ((qOf P : E) ^ M)⁻¹ • (r.symm y - y₀) ∈ stdAt E n P → c = Submodule.Quotient.mk fun a => ι (y (e a)) := by
  intro E k _ _ _ _ _ _ _ P ι ϖ hc A _ _ n e Jl hJo hJ M c y₀
  rintro ⟨g₀, hg₀, y₁, rfl, hy⟩
  rw [Submodule.Quotient.eq] at hy
  let e' : A ⊕ Fin 0 ≃ Fin n := (Equiv.sumEmpty A (Fin 0)).trans e
  have he : ∀ a, e' (.inl a) = e a := fun a => rfl
  have h0 : (g₀⁻¹).val.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁ ∈ box A (ϖ ^ M) := by
    have := neg_mem (GlobalTheory.TwBridge.LevOrb.mulVec_mem_box (hJ (inv_mem hg₀)) _ hy)
    rwa [mulVec_sub, mulVec_mulVec, ← CoupStab.toBlocks₁₁_mul, Units.inv_mul, CoupStab.toBlocks₁₁_one, one_mulVec,
      neg_sub] at this
  have hU2 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k |
      N.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁ ∈ box A (ϖ ^ M)} := by
    refine (CoupStab.isOpen_box (ϖ ^ M)).preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k =>
      N.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁) ?_
    have hb : Continuous fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => N.toBlocks₁₁ :=
      continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inl i) (Sum.inl j)
    exact (hb.matrix_mulVec continuous_const).sub continuous_const
  obtain ⟨U, hU, hUo, hUm⟩ := mem_nhds_iff.1 (image_val_mem_nhds hJo (inv_mem hg₀))
  obtain ⟨M₀, ⟨a1, a2⟩, -⟩ := exists_approx ι hc.dense (g₀⁻¹).val (hUo.inter hU2) ⟨hUm, h0⟩
  obtain ⟨g, hg, ev⟩ := hU a1
  obtain ⟨r, hr⟩ := exists_phi ι e' M₀ g ev
  refine ⟨r, (GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO P ι hc.int e' r).2 ?_, g, hg, ?_, fun y hy' => ?_⟩
  · rw [show GlobalTheory.VolBridge.locHom ι e' r = phi ι e' r from Units.ext rfl, hr]
    exact hJ hg
  · rw [← hr]
    rfl
  · have h1 := GlobalTheory.TwBridge.LevOrb.mulVec_mem_box (hJ hg) _ ((mem_box_iff hc e M _).2 hy')
    rw [Set.mem_setOf_eq, ← ev] at a2
    rw [← hr, phi_mulVec e e' he] at h1 a2
    rw [eq_comm, Submodule.Quotient.eq]
    convert add_mem h1 a2 using 1
    ext a
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, LinearEquiv.apply_symm_apply]
    abel

end GlobalTheory.QPl.RatOrb
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.Rebase
open ValuativeRel

theorem mem_grpAt_of_bc {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (P : GlobalTheory.FinPl.Pl D → Prop) (h : GA D V) (hh : h ∈ GfC V)
    (κ : GL (Fin n) (EF D)) (hκ : finM V hn h = κ.1)
    (hoff : ∀ v, ¬ P v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) κ = 1) : h ∈ GlobalTheory.FinPl.grpAt V P := by
  subst hn
  refine (GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts V P h).2 fun i j => ⟨(GlobalTheory.FinPl.SetCut.mem_GfC_iff_entries V h).1 hh i j, fun w hw => ?_⟩
  have e1 : Formalism.UG.prV (E := D.host.E) w (κ.1 i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun g => g.1 i j) (hoff w hw)
  rw [← hκ, GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply] at e1
  have e2 : Formalism.UG.prV (E := D.host.E) w (toEAf D ((Formalism.L2.Theta.mt V h - 1) i j)) = 0 := by
    rw [Matrix.sub_apply, RingHom.map_sub, map_sub, e1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e3 := (GlobalTheory.StabOff.prV_comm w (finPart D ((Formalism.L2.Theta.mt V h - 1) i j))).symm.trans e2
  exact (map_eq_zero_iff _ (Algebra.TensorProduct.comm _ _ _).injective).1 e3

theorem pr_mem_of_intAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt q.e P) {x : D.host.E}
    (hx : Formalism.L2.Col.IntAt P x) : q.pr (incA D x) ∈ 𝒪[k] := by
  obtain ⟨r, s, hs, e⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ P.asIdeal.zero_mem)
  have hsE : (s : D.host.E) ≠ 0 := fun h => hs0 (RingOfIntegers.coe_eq_zero_iff.mp h)
  have h1 := not_not.1 (mt (GlobalTheory.PhiOneVal.mem_prime_iff_pr_inv_notMem q P hP s hs0).2 hs)
  have e' : x = (r : D.host.E) * (s : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hsE, mul_comm]
    exact e
  rw [e', map_mul, map_mul]
  exact mul_mem (GlobalTheory.LocMod.FullLatFrame.pr_int_mem q r) h1

theorem map_pr_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt q.e P)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (h : GA D V) (r : (Fin n → D.host.E) →ₗ[D.host.E] (Fin n → D.host.E))
    (hr : ∀ i j, adAt D.host.F P (finM V hn h i j) = algebraMap D.host.E _ (r (Pi.single j 1) i))
    {Y : Type} [Fintype Y] [DecidableEq Y] (pos : Y → ℕ) (F : GlobalTheory.LocMod.Frame k V.rank Y) (hF : IsStdFr pos F) (e : Y ≃ Fin n)
    (he : GlobalTheory.SymBridge.IsOrd pos e) :
    (Formalism.L2.Theta.mt V h).map q.pr = F.β * GlobalTheory.SymBridge.toLoc (q.pr.comp (incA D)) e e r * F.γ := by
  subst hn
  obtain ⟨e', he', hF⟩ := hF
  obtain rfl : e = e' := Equiv.ext fun y => Fin.ext ((he y).trans (he' y).symm)
  refine Matrix.ext fun c d => ?_
  obtain ⟨c, rfl⟩ := e.surjective c
  obtain ⟨d, rfl⟩ := e.surjective d
  rw [GlobalTheory.Fam.MovedJoin.mul_frameγ_std _ e hF, GlobalTheory.Fam.MovedJoin.frameβ_mul_std _ e hF]
  have h1 := hr (e c) (e d)
  rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply] at h1
  exact GlobalTheory.SplitProj.pr_eq_of_adAt q P hP _ _ h1

theorem toHom_surj {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) :
    Function.Surjective (toHom S T hS hT) := fun x =>
  ⟨(Matrix.reindex (finCongr hT) (finCongr hS)).symm (LinearMap.toMatrix' x), by
    unfold toHom
    rw [Equiv.apply_symm_apply, Matrix.toLin'_toMatrix']⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

open _root_.Formalism.L2.Col GlobalTheory.StepData GlobalTheory.SymBridge

theorem disjoint_vT (hI : I.Ok) (u : B.Word) (b : I.ι) : Disjoint ((B.primes X).vT u) (rowSG (B.primes X) I.sel (I.tup b)) := by
  refine Finset.disjoint_left.2 fun P h1 h2 => ?_
  obtain ⟨hX, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have h3 := (GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup b) u hX hPr hI.sel_ok
    (hI.T_mem u) hI.g_mem P (Finset.mem_union_left _ h1)).2.2.2.2 h1
  refine GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P ?_ ?_
  · rcases Finset.mem_union.1 h2 with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (I.Q_subset_SQ b h)
  · show algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.asIdeal
    rw [map_natCast]
    exact h3







set_option maxHeartbeats 1000000 in
theorem dead_moved (hI : I.Ok) {b : I.ι} {Ch₀ Ch : ℕ → Type} {A A' : TwDat I l Z u b Ch₀} {ι : ∀ j, Ch j → Ch₀ j} (hl : A.Live ι)
    (hb : A'.b0 = A.b0) (hne : ∀ i, i + 1 ≠ B.R.m → A'.p0 i = A.p0 i)
    (heq : ∀ i, i + 1 = B.R.m → ∀ β, (A'.p0 i β).1.1.deco = (A.p0 i β).1.1.deco ∧ cosetIn (A'.p0 i β) = cosetIn (A.p0 i β)) :
    A'.Live ι := by
  refine ⟨hl.inj, hl.first, hl.last, fun j hj γ hγ α z => ?_⟩
  by_cases h1 : j + 1 = B.R.m
  · refine absurd ?_ hγ
    have : ∀ k, k = B.R.m → Function.Surjective (ι k) := by
      rintro _ rfl
      exact hl.last
    exact this _ h1 γ
  by_cases h2 : j + 2 = B.R.m
  swap
  · have h := hl.dead j hj γ hγ α z
    unfold TwDat.xi at h ⊢
    rw [hb, hne j h1, hne (j + 1) h2]
    exact h
  have hL : (I.idx b).Ok I.Ch I.sel (I.tup b) (I.cst b) I.glob j := by
    have := hI.idx_ok b
    rwa [show B.R.m - 2 = j by omega] at this
  obtain ⟨hd, hc⟩ := heq (j + 1) h2 γ
  have key := GlobalTheory.CplDead.xiCpl1_eq_zero_of_frames I.Ch I.sel (I.tup b) (I.cst b) (I.idx b) I.glob j hL u (disjoint_vT hI u b)
    ((A.b0 j α).get (by omega)) (A.p0 j α).1.1 (A.p0 (j + 1) γ).1.1 (A'.p0 (j + 1) γ).1.1 (A.p0 (j + 1) γ).1.2 (A'.p0 (j + 1) γ).1.2 hd
    (GlobalTheory.AdForm.Rebase.repY_cong h2 _ _ hc) (fun x => ?_)
  · unfold TwDat.xi
    rw [hb, hne j h1]
    unfold xiAt
    rw [dif_neg (by omega), dite_eq_left h2]
    exact (congrArg B.embLL (key _)).trans (map_zero _)
  · obtain ⟨z', hz'⟩ := toHom_surj _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) x
    have h := hl.dead j hj γ hγ α z'
    unfold TwDat.xi xiAt at h
    rw [dif_neg (by omega), dite_eq_left h2] at h
    subst hz'
    exact (map_eq_zero_iff _ B.embLL.injective).1 h


end GlobalTheory.Fam.Rebase

namespace GlobalTheory.Fam
open GlobalTheory.Fam.Rebase


end GlobalTheory.Fam

end
