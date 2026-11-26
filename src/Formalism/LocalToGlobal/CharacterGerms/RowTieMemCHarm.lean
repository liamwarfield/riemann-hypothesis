module

public import Formalism.LocalToGlobal.CharacterGerms.PderivSubGOff
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelfCuts
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEx
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePOAct
public import Formalism.LocalToGlobal.CharacterGerms.TripleSubstSecondCoordinate

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieMemCHarm
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem letter_cast {T : Type} {r : T → ℕ} {n : ℕ} {σ σ' : T} (h : σ = σ') (a : Fin (r σ)) :
    ∃ a' : Fin (r σ'), ∀ b : Fin n, (⟨σ, a, b⟩ : Letter T r n) = ⟨σ', a', b⟩ := by
  subst h
  exact ⟨a, fun b => rfl⟩

section Plane

variable {C : Type} [Field C] {T Orb : Type} [Fintype Orb] {r : T → ℕ} {tau : Orb → ZMod 2 → T}
  {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C} {N n : ℕ} (plc : Fin N × Fin 2 ↪ Fin n)

theorem lap_plane (inj : Function.Injective fun x : Orb × ZMod 2 => tau x.1 x.2)
    (gm_hyp : ∀ o t (s s' : Fin 2), ∑ q, gm o (t + 1) q s * gm o t q s' = if s = s' then 0 else 1)
    (Q : MvPolynomial (Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) C) (o : Orb) (t : ZMod 2)
    (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + 1))))
    (hno : ∀ ρ g1 g2, g1 ≠ g2 → (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ Q.vars →
      (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ Q.vars → False) :
    ∑ b, pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + 1), a2, b⟩ : Letter T r n)
      (subG r tau gm plc Q)) = 0 := by
  have hoff : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ∉ Finset.univ.map plc →
      pderiv (⟨tau o t, a1, b⟩ : Letter T r n) (pderiv (⟨tau o (t + 1), a2, b⟩ : Letter T r n)
        (subG r tau gm plc Q)) = 0 := by
    intro b _ hb
    rw [pderiv_subG_off plc (ℓ := ⟨tau o (t + 1), a2, b⟩), map_zero]
    intro z e
    apply hb
    rw [Finset.mem_map]
    exact ⟨(z.1.1, z.2), Finset.mem_univ _, (congrArg (fun ℓ : Letter T r n => ℓ.2.2) e).symm⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map plc)) hoff, Finset.sum_map, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  have hf : ∀ col, pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n)
      (pderiv (⟨tau o (t + 1), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q)) =
      ∑ g1, ∑ g2, MvPolynomial.C (gm o t col g1 * gm o (t + 1) col g2) *
        subG r tau gm plc (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1))
          (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)) := by
    intro col
    have e2 := pderiv_subG_lam (gm := gm) plc inj ((ρ, ⟨o, ⟨t + 1, a2⟩⟩) : AA r tau N) col Q
    have e2' : pderiv (⟨tau o (t + 1), a2, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc Q) = _ := e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2', map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun g2 _ => ?_
    rw [Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul]
    have e1 := pderiv_subG_lam (gm := gm) plc inj ((ρ, ⟨o, ⟨t, a1⟩⟩) : AA r tau N) col
      (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)
    have e1' : pderiv (⟨tau o t, a1, plc (ρ, col)⟩ : Letter T r n) (subG r tau gm plc
      (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q)) = _ := e1
    rw [e1', Finset.mul_sum]
    refine Finset.sum_congr rfl fun g1 _ => ?_
    rw [map_mul]
    unfold Gm
    ring
  simp only [hf]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun g2 _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_mul, ← map_sum]
  by_cases hg : g1 = g2
  · have hK : ∑ col, gm o t col g1 * gm o (t + 1) col g2 = 0 := by
      have h := gm_hyp o t g2 g1
      rw [if_pos hg.symm] at h
      rw [← h]
      exact Finset.sum_congr rfl fun q _ => mul_comm _ _
    rw [hK, map_zero, zero_mul]
  · have hz : pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1))
        (pderiv ((eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2)) Q) = 0 := by
      by_cases h2 : (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ Q.vars
      · have h1 : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∉ Q.vars := fun h1 => hno ρ g1 g2 hg h1 h2
        rw [pderiv_comm', pderiv_eq_zero_of_notMem_vars h1, map_zero]
      · rw [pderiv_eq_zero_of_notMem_vars h2, map_zero]
    rw [hz, map_zero, mul_zero]

end Plane

section Fam

theorem mem_vars_blkProdG {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V d (I o) (J o)} {F : ∀ o, Flag (X o)} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n} {b : Fin n} {o : Orb} {w : WV (I o)}
    (hx : ((b, ⟨o, w⟩) : Fin n × WVO I) ∈ (blkProd X F n L pl).vars) :
    (b, w) ∈ (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)).vars := by
  first
  | unfold blkProd at hx
  | simp only [blkProd] at hx
  first
  | unfold toAll at hx
  | simp only [toAll] at hx
  have h1 := MvPolynomial.vars_prod _ hx
  rw [Finset.mem_biUnion] at h1
  obtain ⟨o', -, h2⟩ := h1
  have h3 := MvPolynomial.vars_rename _ _ h2
  rw [Finset.mem_image] at h3
  obtain ⟨x, hx1, hx2⟩ := h3
  simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at hx2
  obtain ⟨hb, ho, hw⟩ := hx2
  subst ho
  obtain rfl := eq_of_heq hw
  subst hb
  exact hx1

variable {C : Type} [Field C] {V : VF C} {T : Type} {r : T → ℕ} {cc : T → T} {a : T → ℕ → ℕ}
  {Orb : Type} [Fintype Orb] {tau : Orb → ZMod 2 → T} {gm : Orb → ZMod 2 → Matrix (Fin 2) (Fin 2) C}
  {J : Orb → Fin 2 → Type} [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V 2 (fun _ => IIs r tau o) (J o)} {F : ∀ o, Flag (X o)}
  {gaC : Orb → ZMod 2 → ℕ → ℕ} {N : ℕ} {L : Orb → List (GlobalTheory 2 × ℝ)}
  {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin N}

theorem zmod_two_add_one_add_one_eq : ∀ t : ZMod 2, t + 1 + 1 = t := by
  decide

theorem SelfConjugatePlaceSetting.rowsOK (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (o : Orb) :
    ∃ kind : Fin N → Knd 2, RowsOK (X o).G (X o).Alt
      (prodAll (plAt N pl o) fun i => (blkAt L o i).poly (X o) (F o)) kind := by
  have h : ∀ i : Fin (L o).length, ∃ kind : Fin (rowsAt X L o i) → Knd 2,
      RowsOK (X o).G (X o).Alt ((blkAt L o i).poly (X o) (F o)) kind := by
    intro i
    refine exists_rowsOK (X o) (F o) (Or.inl (H.alt o)) (H.hj o) _ fun g t k hk => ?_
    have hsum : ∀ s, (blkAt L o i).wt (X o) 0 s k + (blkAt L o i).wt (X o) 1 (s + 1) k ≤ gaC o s k := by
      intro s
      rw [← H.wt o s k]
      exact le_sum_map (L o) (fun q => q.1.wt (X o) 0 s k + q.1.wt (X o) 1 (s + 1) k) (List.get_mem (L o) i)
    by_cases hg : g = 0
    · subst hg
      have h1 := hsum t
      exact (H.supp o t k (by omega)).2
    · have hg1 : g = 1 := Fin.eq_one_of_ne_zero g hg
      subst hg1
      have h1 := hsum (t + 1)
      rw [zmod_two_add_one_add_one_eq] at h1
      have h2 := (H.supp o (t + 1) k (by omega)).2
      rw [H.rkF_eq o 0 (t + 1)] at h2
      rw [H.rkF_eq o 1 t]
      exact h2
  choose kind hk using h
  exact ⟨_, rowsOK_prodAll _ _ (plAt_inj N H.plinj o) _ kind hk⟩

theorem lab_eq : ∀ g1 g2 : Fin 2, g1 ≠ g2 → ∀ t : ZMod 2,
    (if g1 = 0 then t else t + 1) = (if g2 = 0 then t + 1 else t + 1 + 1) := by
  decide

theorem SelfConjugatePlaceSetting.no_conj (H : SelfConjugatePlaceSetting r cc a tau gm X F gaC N L pl) (ρ : Fin N) (o : Orb) (g1 g2 : Fin 2) (hne : g1 ≠ g2)
    (t : ZMod 2) (a1 : Fin (r (tau o t))) (a2 : Fin (r (tau o (t + 1))))
    (hx : (eW r tau N).symm ((ρ, ⟨o, ⟨t, a1⟩⟩), g1) ∈ (blkProd X F N L pl).vars)
    (hx' : (eW r tau N).symm ((ρ, ⟨o, ⟨t + 1, a2⟩⟩), g2) ∈ (blkProd X F N L pl).vars) : False := by
  obtain ⟨kind, hk⟩ := H.rowsOK o
  have hx1 : ((ρ, ⟨o, ⟨g1, ⟨t, a1⟩⟩⟩) : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ∈ (blkProd X F N L pl).vars := hx
  have hx2 : ((ρ, ⟨o, ⟨g2, ⟨t + 1, a2⟩⟩⟩) : Fin N × WVO fun o (_ : Fin 2) => IIs r tau o) ∈ (blkProd X F N L pl).vars := hx'
  have h1 := mem_vars_blkProdG hx1
  have h2 := mem_vars_blkProdG hx2
  have ht : tyW (X o).G (⟨g1, ⟨t, a1⟩⟩ : WV fun _ => IIs r tau o) = tyW (X o).G (⟨g2, ⟨t + 1, a2⟩⟩ : WV fun _ => IIs r tau o) :=
    (H.hty o g1 ⟨t, a1⟩).trans ((lab_eq g1 g2 hne t).trans (H.hty o g2 ⟨t + 1, a2⟩).symm)
  exact no_conj_of_rowsOK hk h1 h2 hne ht

end Fam

theorem isotropic_to_std_subst_harmonic : IsotropicToStdSubstHarmonic := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc isX
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ _ a1 a2
  rw [lap_one_apply]
  have hdiag : ∀ b, (∑ b', (1 : Matrix (Fin n) (Fin n) C) b b' •
      pderiv (⟨τ, a1, b⟩ : Letter T r n) (pderiv (⟨cc τ, a2, b'⟩ : Letter T r n)
        (subG r tau gm plc (blkProd X F N L pl)))) =
      pderiv (⟨τ, a1, b⟩ : Letter T r n) (pderiv (⟨cc τ, a2, b⟩ : Letter T r n)
        (subG r tau gm plc (blkProd X F N L pl))) := by
    intro b
    rw [Finset.sum_eq_single b]
    · rw [Matrix.one_apply_eq, one_smul]
    · intro b' _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [hdiag]
  by_cases hτ : ∃ o t, tau o t = τ
  · obtain ⟨o, t, rfl⟩ := hτ
    obtain ⟨a2', ha2⟩ := letter_cast (n := n) (H.conj o t) a2
    simp only [ha2]
    exact lap_plane plc H.inj H.gm_hyp _ o t a1 a2' fun ρ g1 g2 hne h1 h2 => H.no_conj ρ o g1 g2 hne t a1 a2' h1 h2
  · push Not at hτ
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [pderiv_comm', pderiv_subG_off plc (ℓ := ⟨τ, a1, b⟩), map_zero]
    intro z e
    exact hτ _ _ (congrArg Sigma.fst e).symm

end Formalism.L2.FormalSeriesBounds.RF
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RankMaximalOfNondegenerateOfUnitSeriesIntegral
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Defs

variable {C : Type} [Field C]

def mulL {dd : ℕ} (F : Fin dd → PS C 2 dd) : ℕ → Pt C 1 dd
  | 0 => fun _ => 0
  | n + 1 => addOf F (mulL F n) (pt C dd 0)

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def FBChart.u1 (Y : FBChart C V O dd) : PS C 2 dd :=
  FB.expS C (ev (n := 2) ![comp1 (mulL Y.B.G.F V.l) (pt C (n := 2) dd 0), pt C dd 1] Y.h - (V.l : C) • Y.h)

def FBChart.aOf (Y : FBChart C V O dd) (u : Fin dd → C) : PS C 1 dd :=
  fun ν => ∑ i, u i ^ V.l * MvPowerSeries.coeff
    (Finsupp.single ((0 : Fin 2), i) V.l + ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1

end Defs

def FirstUnitSeriesIntegral : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd), IntS V Y.u1

def FirstUnitSeriesFrobenius : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (μ : Fin 2 × Fin dd →₀ ℕ), (∃ i, ¬ V.l ∣ μ ((0 : Fin 2), i)) →
      V.MM (MvPowerSeries.coeff μ Y.u1)

def MulLFrobSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (k : Fin dd) (μ : Fin 1 × Fin dd →₀ ℕ), (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) →
      V.MM (MvPowerSeries.coeff μ (mulL Y.B.G.F V.l k))

theorem intS_aOf {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (h : IntS V Y.u1) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) : IntS V (Y.aOf u) := by
  intro ν
  show V.Ge 0 (∑ i, u i ^ V.l * MvPowerSeries.coeff
    (Finsupp.single ((0 : Fin 2), i) V.l + ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1)
  exact VF.Ge.sum fun i _ => by simpa using ((hu i).pow V.l).mul (h _)

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelfEx
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePLimSelf
noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem limSelf_holds : LimSelfSt := by
  unfold LimSelfSt AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p g x x' hx hlim
  exact LimTy.lim_mem (Y.rawSelf p) V.l_prime.two_le
    (fun i => FBChart.self_chart_log_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.self_chart_exp_constantCoeff (Y := Y) (p := p) i)
    (fun i => FBChart.rawSelf_lgex (Y := Y) (p := p) i)
    (fun i => FBChart.rawSelf_exlg (Y := Y) (p := p) i)
    g x x' hx hlim

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

def AllStartSelfSt : Prop :=
  AllSelf fun C _ V _ I _ _ X => ∀ (g : Fin 2) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    ∃ L ∈ X.AllSet V g, ∀ c, L 1 (Sum.inl c) = w c

theorem ptExSelf_of_start (hS : AllStartSelfSt) : PTExSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g a w hw _
  obtain ⟨L0, hL0, hL01⟩ := hS C V O dd Y d I0 p g w hw
  set X := Y.rawSelf p with hX
  let M : Set (ℕ → I0 ⊕ I0 → C) := {m | ∀ L ∈ X.AllSet V g, m * L ∈ X.AllSet V g}
  have hAdd := addCvSelf_holds C V O dd Y d I0 p
  have h1 : (1 : ℕ → I0 ⊕ I0 → C) ∈ M := fun L hL => by rwa [one_mul]
  have hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M := fun m m' hm hm' L hL => by
    rw [add_mul]; exact X.allSet_add V g hAdd (fun g c x => Y.rawSelf_u_integral p g c x) (hm L hL) (hm' L hL)
  have hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M := fun m m' hm hm' L hL => by
    rw [mul_assoc]; exact hm _ (hm' L hL)
  have hteich : ∀ c : C, V.Ge 0 c → (fun n (_ : I0 ⊕ I0) => c ^ n) ∈ M := fun c hc L hL =>
    X.allSet_teich V g c hc hL
  have hlim : ∀ (m : ℕ → ℕ → I0 ⊕ I0 → C) (m' : ℕ → I0 ⊕ I0 → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M :=
    fun m m' hm hmm' L hL => X.allSet_lim (Y.self_chart_log_constantCoeff p) (Y.self_chart_exp_constantCoeff p) (Y.rawSelf_lgex p) (Y.rawSelf_exlg p)
      (fun k => hm k L hL) (hmm'.mul_right L)
  have hroot : ∀ q : ℕ, q.Prime → q ≠ V.l → ∃ ζ : C, IsPrimitiveRoot ζ q := by
    intro q hq _
    have := Y.algClosed
    have : NeZero (q : C) := ⟨Nat.cast_ne_zero.mpr hq.ne_zero⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot C q
  have hind := TypAr.typ_gen M hroot h1 hadd hmul hteich hlim
  have hL := hind L0 hL0
  refine ⟨_, X.typ_link V g hL ?_, ?_⟩
  · intro n k hn
    simp only [Pi.mul_apply]
    rw [if_neg hn, zero_mul]
  · intro c
    simp only [Pi.mul_apply, pow_zero]
    rw [if_pos ⟨0, pow_zero _⟩, one_mul, hL01 c]

theorem ptSelf_of_start (hS : AllStartSelfSt) (hAct : OActSelfSt) (hStab : HStabSelfSt) : PTSelfSt :=
  ptSelf_of_act (ptExSelf_of_start hS) hAct limSelf_holds hStab

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace OActSelf

open PartialDerivEval LogEx OActLog OActSg OAct

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem linAct_smul (φ : Pt C 1 dd) (c : C) (w : Fin dd → C) : linAct φ (c • w) = c • linAct φ w := by
  funext i
  simp only [linAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cc_dh (Y : FBChart C V O dd) (i : Fin dd) : constantCoeff (pderiv ((1 : Fin 2), i) Y.h) = 0 := by
  let a : Fin 2 → Pt C 1 dd := ![0, pt C dd 0]
  have hZ : Z0 a := constant_zero_zero_point (pt C dd 0) (coordinate_point_constantCoeff 0)
  have hchain : pderiv ((0 : Fin 1), i) (ev a Y.h) =
      ∑ p : Fin 2 × Fin dd, ev a (pderiv p Y.h) * pderiv ((0 : Fin 1), i) (a p.1 p.2) := by
    unfold ev
    exact Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin dd => a p.1 p.2)
      (fun p => hZ p.1 p.2) Y.h ((0 : Fin 1), i)
  have hderiv : pderiv ((0 : Fin 1), i) (ev a Y.h) = ev a (pderiv ((1 : Fin 2), i) Y.h) := by
    rw [hchain, Finset.sum_eq_single ((1 : Fin 2), i)]
    · change _ * pderiv ((0 : Fin 1), i) (X ((0 : Fin 1), i)) = _
      rw [pderiv_X_self, mul_one]
    · rintro ⟨k, j⟩ _ hne
      fin_cases k
      · change _ * pderiv ((0 : Fin 1), i) (0 : PS C 1 dd) = 0
        rw [map_zero, mul_zero]
      · have hji : j ≠ i := by
          intro h
          subst j
          exact hne rfl
        change _ * pderiv ((0 : Fin 1), i) (X ((0 : Fin 1), j)) = 0
        rw [pderiv_X_of_ne (by simpa using hji), mul_zero]
    · simp
  have h0 := congrArg (pderiv ((0 : Fin 1), i)) Y.gauge.ax0
  change pderiv ((0 : Fin 1), i) (ev a Y.h) = _ at h0
  rw [hderiv, map_zero] at h0
  simpa only [constantCoeff_ev hZ, map_zero] using congrArg constantCoeff h0

theorem cc_sgP (Y : FBChart C V O dd) (w : Fin dd → C) : constantCoeff (Y.sgP w) = 0 := by
  unfold FBChart.sgP
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_neg, map_sum, map_mul, constantCoeff_ev constant_zero_first_zero, cc_dh, mul_zero, Finset.sum_const_zero, neg_zero]

def actCv (Y : FBChart C V O dd) (β : O) (γ : Fin dd → PowerSeries C) : Fin dd → PowerSeries C :=
  fun j => alongCv γ (un1 (Y.B.A.act β j))

section Col

variable (Y : FBChart C V O dd) (β : O) {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ)
include hγ

theorem actCv_cv : IsCv V (actCv Y β γ) := fun j =>
  ⟨constantCoeff_subst_zero (fun j => (hγ j).1) (by rw [constantCoeff_uncurry, Y.B.A.const β j]),
    intS_ps.1 (IntS.subst (fun j => (hγ j).1) (fun j => intS_ps.2 (hγ j).2) (integralSeries_uncurry_one (Y.intAct β j)))⟩

theorem actCv_comp (f : PS C 1 dd) :
    alongCv (actCv Y β γ) (un1 f) = alongCv γ (un1 (ev (n := 1) ![Y.B.A.act β] f)) := by
  have hφ0 : ∀ j, constantCoeff (Y.B.A.act β j) = 0 := Y.B.A.const β
  have hφu0 : ∀ j, constantCoeff (un1 (Y.B.A.act β j)) = 0 := fun j => by rw [constantCoeff_uncurry, hφ0 j]
  have hSγ : HasSubst γ := hasSubst_of_constantCoeff_zero fun j => (hγ j).1
  unfold actCv alongCv
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hφu0) hSγ]
  congr 1
  rw [subst_singlePointUncurry hφu0, eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun p : Fin 1 × Fin dd => Y.B.A.act β p.2) (fun p => hφ0 p.2)]

theorem along_Cmul (c : C) (f : MvPowerSeries (Fin dd) C) : alongCv γ (MvPowerSeries.C c * f) = c • alongCv γ f := by
  have hSγ : HasSubst γ := hasSubst_of_constantCoeff_zero fun j => (hγ j).1
  unfold alongCv
  rw [← MvPowerSeries.smul_eq_C_mul, ← coe_substAlgHom hSγ, map_smul]

theorem along_sub (f f' : MvPowerSeries (Fin dd) C) : alongCv γ (f - f') = alongCv γ f - alongCv γ f' := by
  have hSγ : HasSubst γ := hasSubst_of_constantCoeff_zero fun j => (hγ j).1
  unfold alongCv
  rw [← coe_substAlgHom hSγ, map_sub]

theorem actCv_lg (i : Fin dd) :
    alongCv (actCv Y β γ) (un1 (Y.lg i)) = ∑ j, linM (Y.B.A.act β) i j • alongCv γ (un1 (Y.lg j)) := by
  have hSγ : HasSubst γ := hasSubst_of_constantCoeff_zero fun j => (hγ j).1
  rw [actCv_comp Y β hγ, show ev (n := 1) ![Y.B.A.act β] (Y.lg i) = comp1 Y.lg (Y.B.A.act β) i from rfl,
    log_endo Y.B.G Y.lg Y.lg_lin Y.lg_add (Y.B.A.act β) (Y.B.A.const β) (Y.B.A.hom β) i, uncurry_linear_combination]
  have e : alongCv γ (∑ j, MvPowerSeries.C (linM (Y.B.A.act β) i j) * un1 (Y.lg j)) =
      ∑ j, alongCv γ (MvPowerSeries.C (linM (Y.B.A.act β) i j) * un1 (Y.lg j)) := by
    unfold alongCv
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← coe_substAlgHom hSγ, map_sum]
  rw [e]
  exact Finset.sum_congr rfl fun j _ => along_Cmul hγ _ _

theorem actCv_sg (v : Fin dd → C) (hv : ∀ i, V.Ge 0 (v i)) (e : C)
    (he : linAct (Y.B.A.act (star β)) v = e • v) :
    ∃ Δ : PowerSeries C, PowerSeries.constantCoeff Δ = 0 ∧ (∀ n, V.Ge 0 (PowerSeries.coeff n Δ)) ∧
      alongCv (actCv Y β γ) (un1 (Y.sgP v)) = e • alongCv γ (un1 (Y.sgP v)) + Δ := by
  refine ⟨alongCv γ (un1 (ev (n := 1) ![Y.B.A.act β] (Y.sgP v) - Y.sgP (linAct (Y.B.A.act (star β)) v))), ?_, ?_, ?_⟩
  · refine constantCoeff_subst_zero (fun j => (hγ j).1) ?_
    rw [constantCoeff_uncurry, map_sub, constantCoeff_ev (z0_1 _ (Y.B.A.const β)), cc_sgP, cc_sgP, sub_zero]
  · exact intS_ps.1 (IntS.subst (fun j => (hγ j).1) (fun j => intS_ps.2 (hγ j).2) (integralSeries_uncurry_one (sg_act Y β v hv)))
  · rw [actCv_comp Y β hγ, uncurry_sub, along_sub hγ, he, sgP_smul, uncurry_C_mul, along_Cmul hγ]
    abel

end Col

section Chars

variable {Y : FBChart C V O dd} {d : ℕ} {I0 : Type} [Fintype I0]

theorem char_l (p : SelfData Y d I0) (g : Fin 2) (α : O) (c : I0) :
    p.em (p.ty0 c) (if g = 0 then α else star α) = p.em ((Y.rawSelf p).ty g c) α := by
  fin_cases g
  · simp [FBChart.rawSelf]
  · simp [FBChart.rawSelf, p.em_conj]

theorem char_r (p : SelfData Y d I0) (g : Fin 2) (α : O) (q : I0) :
    p.em (p.ty0 q) (star (if g = 0 then α else star α)) = p.em ((Y.rawSelf p).ty (1 - g) q) α := by
  fin_cases g
  · simp [FBChart.rawSelf, p.em_conj]
  · simp [FBChart.rawSelf]

end Chars

theorem oActSelf_holds : OActSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g α x hx
  obtain ⟨γ, lam, hγ, hlam, hlg, hsg⟩ := hx
  obtain ⟨β, hβ⟩ : ∃ β : O, β = if g = 0 then α else star α := ⟨_, rfl⟩
  have hcl : ∀ c, p.em (p.ty0 c) β = p.em ((Y.rawSelf p).ty g c) α := fun c => by rw [hβ]; exact char_l p g α c
  have hcr : ∀ q, p.em (p.ty0 q) (star β) = p.em ((Y.rawSelf p).ty (1 - g) q) α := fun q => by
    rw [hβ]; exact char_r p g α q
  have hγc : ∀ col, IsCv V (fun i => γ (col, i)) := fun col i => hγ (col, i)
  set γ' : Fin 2 × Fin dd → PowerSeries C := fun z => actCv Y β (fun i => γ (z.1, i)) z.2 with hγ'def
  have hγ'cv : IsCv V γ' := fun z => actCv_cv Y β (hγc z.1) z.2
  have hγ'c : ∀ col, (fun i => γ' (col, i)) = actCv Y β (fun i => γ (col, i)) := fun col => rfl
  have along : ∀ δ : Fin 2 × Fin dd → PowerSeries C, IsCv V δ → ∀ c (f : MvPowerSeries (Fin dd) C),
      alongCv δ (inCol c f) = alongCv (fun i => δ (c, i)) f :=
    fun δ hδ c f => subst_inCol (fun z => (hδ z).1) c f
  have hsum : ∀ δ : Fin 2 × Fin dd → PowerSeries C, IsCv V δ → ∀ f : Fin 2 → MvPowerSeries (Fin dd) C,
      alongCv δ (∑ c, inCol c (f c)) = ∑ c, alongCv (fun i => δ (c, i)) (f c) := by
    intro δ hδ f
    have hS := hasSubst_of_constantCoeff_zero fun z => (hδ z).1
    unfold alongCv
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← MvPowerSeries.coe_substAlgHom hS, map_sum, MvPowerSeries.coe_substAlgHom hS]
    exact Finset.sum_congr rfl fun c _ => along δ hδ c (f c)

  have he_col : ∀ (q : I0) (col : Fin 2), linAct (Y.B.A.act (star β)) (fun i => (Y.rawSelf p).u (1 - g) q (col, i)) =
      p.em ((Y.rawSelf p).ty (1 - g) q) α • (fun i => (Y.rawSelf p).u (1 - g) q (col, i)) := by
    intro q col
    show linAct (Y.B.A.act (star β)) (p.gm (p.ty0 q) col (1 - g) • p.e q) =
      p.em ((Y.rawSelf p).ty (1 - g) q) α • (p.gm (p.ty0 q) col (1 - g) • p.e q)
    rw [linAct_smul, p.e_eig q (star β), hcr q, smul_comm]
  choose Δ hΔ0 hΔi hΔeq using fun (q : I0) (col : Fin 2) =>
    actCv_sg Y β (hγc col) (fun i => (Y.rawSelf p).u (1 - g) q (col, i))
      (fun i => Y.rawSelf_u_integral p (1 - g) q (col, i)) _ (he_col q col)
  have hE : ∀ q : I0, alongCv γ' ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) =
      p.em ((Y.rawSelf p).ty (1 - g) q) α • alongCv γ ((Y.rawSelf p).sg ((Y.rawSelf p).u (1 - g) q)) +
        ∑ col, Δ q col := by
    intro q
    rw [Y.rawSelf_sg p, hsum γ' hγ'cv, hsum γ hγ, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun col _ => ?_
    rw [Y.rawCol_sg, hγ'c col, hΔeq q col]
  set lam' : I0 → PowerSeries C := fun q => p.em ((Y.rawSelf p).ty (1 - g) q) α • lam q + ∑ col, Δ q col
    with hlam'def
  have hlam'cv : IsCv V lam' := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · rw [hlam'def]
      simp only
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_add (f := _), PowerSeries.coeff_smul,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, (hlam q).1, map_sum]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hΔ0, Finset.sum_const_zero, smul_eq_mul, mul_zero,
        add_zero]
    · rw [hlam'def]
      simp only
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_add (f := _), PowerSeries.coeff_smul, smul_eq_mul, map_sum]
      exact ((p.em_int _ α).mul_int ((hlam q).2 n)).add (VF.Ge.sum fun col _ => hΔi q col n)
  refine ⟨γ', lam', hγ'cv, hlam'cv, fun z => ?_, fun q => ?_⟩
  ·
    obtain ⟨col, i⟩ := z
    simp only [tyS_smul, RawChart.tyC, Sum.elim_inl]
    have hu : ∀ c, ∑ j, linM (Y.B.A.act β) i j * (Y.rawSelf p).u g c (col, j) =
        p.em ((Y.rawSelf p).ty g c) α * (Y.rawSelf p).u g c (col, i) := by
      intro c
      have h1 : ∑ j, linM (Y.B.A.act β) i j * p.e c j = p.em (p.ty0 c) β * p.e c i := congrFun (p.e_eig c β) i
      show ∑ j, linM (Y.B.A.act β) i j * (p.gm (p.ty0 c) col g * p.e c j) =
        p.em ((Y.rawSelf p).ty g c) α * (p.gm (p.ty0 c) col g * p.e c i)
      calc ∑ j, linM (Y.B.A.act β) i j * (p.gm (p.ty0 c) col g * p.e c j)
          = p.gm (p.ty0 c) col g * ∑ j, linM (Y.B.A.act β) i j * p.e c j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ = p.gm (p.ty0 c) col g * (p.em (p.ty0 c) β * p.e c i) := by rw [h1]
        _ = p.em ((Y.rawSelf p).ty g c) α * (p.gm (p.ty0 c) col g * p.e c i) := by rw [hcl c]; ring
    rw [show (Y.rawSelf p).lg (col, i) = inCol col (un1 (Y.lg i)) from rfl, along γ' hγ'cv, hγ'c col,
      actCv_lg Y β (hγc col)]
    simp only [show ∀ j, alongCv (fun i => γ (col, i)) (un1 (Y.lg j)) = alongCv γ ((Y.rawSelf p).lg (col, j)) from
      fun j => (along γ hγ col _).symm, hlg, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_smul, hu c, mul_comm]
  ·
    simp only [tyS_smul, RawChart.tyC, Sum.elim_inl, Sum.elim_inr]
    rw [hsg q, hE q, hlam'def]
    simp only
    rw [smul_add, smul_sub, Finset.smul_sum]
    have hs : ∀ c : I0, p.em ((Y.rawSelf p).ty (1 - g) q) α •
        (if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
          (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c))
          else 0) =
        if (Y.rawSelf p).ty g c = (Y.rawSelf p).ty (1 - g) q then
          (Y.rawSelf p).sg1 ((Y.rawSelf p).u g c) ((Y.rawSelf p).u (1 - g) q) •
            (p.em ((Y.rawSelf p).ty g c) α • tyS V.l (fun s => x s (Sum.inl c))) else 0 := by
      intro c
      split_ifs with h
      · rw [h, smul_comm]
      · rw [smul_zero]
    rw [Finset.sum_congr rfl fun c _ => hs c]
    abel

end OActSelf

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.FirstPartialLawAtPoints
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

variable (Y : FBChart C V O dd)

section Three

variable {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)

include ha hb hc

theorem first_partial_law_at_points : MvPowerSeries.subst (P3 a b c) Y.B.ph1 =
    mvExp (hAt Y a c + hAt Y b c - hAt Y (addAt Y a b) c) := by
  have h := Y.gauge.ph1
  rw [toK_eq, eval_two_points_eq_subst _ _ _ rfl, eval_two_points_eq_subst _ _ _ rfl, eval_two_points_eq_subst _ _ _ rfl, addOf_eq] at h
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 3)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 3)
  have k2 := cc_pt (C := C) (dd := dd) (2 : Fin 3)
  have hcc : MvPowerSeries.constantCoeff (hAt Y (pt C dd (0 : Fin 3)) (pt C dd (2 : Fin 3)) +
      hAt Y (pt C dd (1 : Fin 3)) (pt C dd (2 : Fin 3)) -
      hAt Y (addAt Y (pt C dd (0 : Fin 3)) (pt C dd (1 : Fin 3))) (pt C dd (2 : Fin 3))) = 0 := by
    rw [map_sub, map_add (f := _), cc_hAt Y k0 k2, cc_hAt Y k1 k2, cc_hAt Y (cc_addAt Y k0 k1) k2]
    simp
  have h' : Y.B.ph1 = FB.expS C (hAt Y (pt C dd (0 : Fin 3)) (pt C dd (2 : Fin 3)) +
      hAt Y (pt C dd (1 : Fin 3)) (pt C dd (2 : Fin 3)) -
      hAt Y (addAt Y (pt C dd (0 : Fin 3)) (pt C dd (1 : Fin 3))) (pt C dd (2 : Fin 3))) := h
  have hP := constantCoeff_triple_substitution ha hb hc
  rw [h', expS_eq _ hcc, subst_exp hP hcc, subst_sub' hP, subst_add' hP, hAt_subst Y hP k0 k2, hAt_subst Y hP k1 k2,
    hAt_subst Y hP (cc_addAt Y k0 k1) k2, triple_subst_first_coordinate ha hb hc, triple_subst_second_coordinate ha hb hc, triple_subst_third_coordinate ha hb hc]
  congr 3
  funext i
  rw [addAt_subst Y hP k0 k1, triple_subst_first_coordinate ha hb hc, triple_subst_second_coordinate ha hb hc]

end Three

theorem hAt_zero_left {c : Fin dd → MvPowerSeries τ C} (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0) :
    hAt Y (fun _ => 0) c = 0 := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => c q.2) := by
    first
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun q => hc q.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
          (fun q => by rw [hc q.2]; exact IsNilpotent.zero)
      | exact ⟨fun q => by rw [hc q.2]; exact IsNilpotent.zero,
          by first
            | exact fun d => Set.toFinite _
            | (simp only [Set.finite_coe_iff]; intro d; exact Set.toFinite _)
            | (simp; intro d; exact Set.toFinite _)⟩
  have h1 : MvPowerSeries.subst (P2 (0 : Pt C 1 dd) (pt C dd 0)) Y.h = 0 := by
    rw [← eval_two_points_eq_subst (m := 2) _ _ _ rfl]
    exact Y.gauge.ax0
  have h3 : hAt Y (fun _ => 0) c =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => c q.2) (MvPowerSeries.subst (P2 (0 : Pt C 1 dd) (pt C dd 0)) Y.h) := by
    rw [subst_pair_substitution_comm]
    · unfold hAt
      congr 2
      · funext i
        rw [Pi.zero_apply, ← MvPowerSeries.coe_substAlgHom hA, map_zero]
      · funext i
        first
          | simp [pt, MvPowerSeries.subst_X hA]
          | (unfold pt; simp [MvPowerSeries.subst_X hA])
          | rfl
    all_goals first
      | exact hA
      | (intro i; simp [pt])
      | (intro i; rfl)
      | simp_all
      | skip
  rw [h3, h1, ← MvPowerSeries.coe_substAlgHom hA, map_zero]

theorem hAt_zero_right {c : Fin dd → MvPowerSeries τ C} (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0) :
    hAt Y c (fun _ => 0) = 0 := by
  have hA : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => c q.2) := by
    first
      | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (fun q => hc q.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent
          (fun q => by rw [hc q.2]; exact IsNilpotent.zero)
      | exact ⟨fun q => by rw [hc q.2]; exact IsNilpotent.zero,
          by first
            | exact fun d => Set.toFinite _
            | (simp only [Set.finite_coe_iff]; intro d; exact Set.toFinite _)
            | (simp; intro d; exact Set.toFinite _)⟩
  have h1 : MvPowerSeries.subst (P2 (pt C dd 0) (0 : Pt C 1 dd)) Y.h = 0 := by
    rw [← eval_two_points_eq_subst (m := 2) _ _ _ rfl]
    exact Y.gauge.ax1
  have h3 : hAt Y c (fun _ => 0) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => c q.2) (MvPowerSeries.subst (P2 (pt C dd 0) (0 : Pt C 1 dd)) Y.h) := by
    rw [subst_pair_substitution_comm]
    · unfold hAt
      congr 2
      · funext i
        first
          | simp [pt, MvPowerSeries.subst_X hA]
          | (unfold pt; simp [MvPowerSeries.subst_X hA])
          | rfl
      · funext i
        rw [Pi.zero_apply, ← MvPowerSeries.coe_substAlgHom hA, map_zero]
    all_goals first
      | exact hA
      | (intro i; simp [pt])
      | (intro i; rfl)
      | simp_all
      | skip
  rw [h3, h1, ← MvPowerSeries.coe_substAlgHom hA, map_zero]

def GoodPt (V : VF C) (a : Fin dd → MvPowerSeries τ C) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (a i) = 0) ∧ ∀ i, IntS V (a i)

private theorem intS_subst_of_intS {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (ha : ∀ s, IntS V (a s)) {f : MvPowerSeries σ C}
    (hf : IntS V f) : IntS V (MvPowerSeries.subst a f) := by
  first
    | exact IntS.subst ha0 ha hf
    | exact PartialDerivEval.intS_subst ha0 ha hf
    | exact AltInv.intS_subst ha0 ha hf

theorem GoodPt.add {a b : Fin dd → MvPowerSeries τ C} (ha : GoodPt V a) (hb : GoodPt V b) : GoodPt V (addAt Y a b) := by
  have h0 : ∀ q, MvPowerSeries.constantCoeff (P2 a b q) = 0 := by
    intro q
    unfold P2
    split_ifs
    · exact ha.1 _
    · exact hb.1 _
  have hI : ∀ q, IntS V (P2 a b q) := by
    intro q
    unfold P2
    split_ifs
    · exact ha.2 _
    · exact hb.2 _
  refine ⟨fun i => cc_addAt Y ha.1 hb.1 i, fun i => ?_⟩
  show IntS V (MvPowerSeries.subst (P2 a b) (Y.B.G.F i))
  exact intS_subst_of_intS h0 hI (Y.intF i)

theorem GoodPt.zero : GoodPt V (fun _ : Fin dd => (0 : MvPowerSeries τ C)) := by
  refine ⟨fun _ => map_zero _, fun _ => ?_⟩
  unfold IntS
  intro μ
  rw [map_zero]
  unfold VF.Ge
  first
    | simp
    | exact le_top
    | (simp [VF.v]; done)

theorem GoodPt.act (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : GoodPt V a) : GoodPt V (actAt Y x a) := by
  refine ⟨fun i => cc_actAt Y x ha.1 i, fun i => ?_⟩
  show IntS V (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act x i))
  exact intS_subst_of_intS (a := fun q : Fin 1 × Fin dd => a q.2) (fun q => ha.1 q.2) (fun q => ha.2 q.2)
    (Y.intAct x i)

def sumL : List (Fin dd → MvPowerSeries τ C) → (Fin dd → MvPowerSeries τ C)
  | [] => fun _ => 0
  | a :: l => addAt Y a (sumL l)

theorem good_sumL : ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) → GoodPt V (sumL Y l)
  | [], _ => GoodPt.zero
  | a :: l, h => (h a List.mem_cons_self).add Y (good_sumL l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem isIU_of_exp {U f : MvPowerSeries τ C} (hi : IntS V U) (he : U = mvExp f) : IsIU V U := by
  refine ⟨hi, ?_⟩
  subst he
  unfold mvExp
  have h1 : (MvPowerSeries.constantCoeff fun m : τ →₀ ℕ =>
      ∑ k ∈ Finset.range (Finsupp.degree m + 1), (MvPowerSeries.coeff m) (f ^ k) / (k.factorial : C)) = 1 := by
    show (∑ k ∈ Finset.range (Finsupp.degree (0 : τ →₀ ℕ) + 1),
      (MvPowerSeries.coeff (0 : τ →₀ ℕ)) (f ^ k) / (k.factorial : C)) = 1
    simp
  rw [h1]
  first
    | simp
    | exact map_one _
    | rfl
    | (simp [VF.v]; done)

theorem biadd_left {c : Fin dd → MvPowerSeries τ C} (hc : GoodPt V c) :
    ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) →
      ∃ U : MvPowerSeries τ C, IsIU V U ∧ mvExp (hAt Y (sumL Y l) c) * U = (l.map fun a => mvExp (hAt Y a c)).prod := by
  intro l
  induction l with
  | nil =>
      intro _
      refine ⟨1, IsIU.one, ?_⟩
      show mvExp (hAt Y (fun _ => 0) c) * 1 = 1
      rw [hAt_zero_left Y hc.1, rtj_mvExp_zero, one_mul]
  | cons a l ih =>
      intro h
      have ha : GoodPt V a := h a (List.mem_cons_self (a := a) (l := l))
      have hl := good_sumL Y l fun b hb => h b (List.mem_cons_of_mem _ hb)
      obtain ⟨U, hU, e⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hp := first_partial_law_at_points Y ha.1 hl.1 hc.1
      have hpi : IntS V (MvPowerSeries.subst (P3 a (sumL Y l) c) Y.B.ph1) :=
        IntS.subst (constantCoeff_triple_substitution ha.1 hl.1 hc.1) (integral_triple_substitution ha.2 hl.2 hc.2) Y.intPh1
      refine ⟨MvPowerSeries.subst (P3 a (sumL Y l) c) Y.B.ph1 * U, (isIU_of_exp hpi hp).mul hU, ?_⟩
      have c1 := cc_hAt Y ha.1 hc.1
      have c2 := cc_hAt Y hl.1 hc.1
      have c3 := cc_hAt Y (cc_addAt Y ha.1 hl.1) hc.1
      have e2 : mvExp (hAt Y (addAt Y a (sumL Y l)) c) * MvPowerSeries.subst (P3 a (sumL Y l) c) Y.B.ph1 =
          mvExp (hAt Y a c) * mvExp (hAt Y (sumL Y l) c) := by
        rw [hp, ← exp_add c3 (by rw [map_sub, map_add (f := _), c1, c2, c3]; simp), ← exp_add c1 c2]
        congr 1
        ring
      show mvExp (hAt Y (addAt Y a (sumL Y l)) c) * _ = _
      rw [List.map_cons, List.prod_cons, ← e, ← mul_assoc, e2, mul_assoc]

theorem biadd_right {c : Fin dd → MvPowerSeries τ C} (hc : GoodPt V c) :
    ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) →
      ∃ U : MvPowerSeries τ C, IsIU V U ∧ mvExp (hAt Y c (sumL Y l)) * U = (l.map fun a => mvExp (hAt Y c a)).prod := by
  intro l
  induction l with
  | nil =>
      intro _
      refine ⟨1, IsIU.one, ?_⟩
      show mvExp (hAt Y c (fun _ => 0)) * 1 = 1
      rw [hAt_zero_right Y hc.1, rtj_mvExp_zero, one_mul]
  | cons a l ih =>
      intro h
      have ha : GoodPt V a := h a (List.mem_cons_self (a := a) (l := l))
      have hl := good_sumL Y l fun b hb => h b (List.mem_cons_of_mem _ hb)
      obtain ⟨U, hU, e⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
      have hp := second_partial_law_at_points Y hc.1 ha.1 hl.1
      have hpi : IntS V (MvPowerSeries.subst (P3 c a (sumL Y l)) Y.B.ph2) :=
        IntS.subst (constantCoeff_triple_substitution hc.1 ha.1 hl.1) (integral_triple_substitution hc.2 ha.2 hl.2) Y.intPh2
      refine ⟨MvPowerSeries.subst (P3 c a (sumL Y l)) Y.B.ph2 * U, (isIU_of_exp hpi hp).mul hU, ?_⟩
      have c1 := cc_hAt Y hc.1 ha.1
      have c2 := cc_hAt Y hc.1 hl.1
      have c3 := cc_hAt Y hc.1 (cc_addAt Y ha.1 hl.1)
      have e2 : mvExp (hAt Y c (addAt Y a (sumL Y l))) * MvPowerSeries.subst (P3 c a (sumL Y l)) Y.B.ph2 =
          mvExp (hAt Y c a) * mvExp (hAt Y c (sumL Y l)) := by
        rw [hp, ← exp_add c3 (by rw [map_sub, map_add (f := _), c1, c2, c3]; simp), ← exp_add c1 c2]
        congr 1
        ring
      show mvExp (hAt Y c (addAt Y a (sumL Y l))) * _ = _
      rw [List.map_cons, List.prod_cons, ← e, ← mul_assoc, e2, mul_assoc]

end VP

end Formalism.L2.FormalSeriesBounds
end
end
