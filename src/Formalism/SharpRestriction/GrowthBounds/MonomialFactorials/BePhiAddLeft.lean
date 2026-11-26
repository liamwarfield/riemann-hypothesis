module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BejjSmulLeft
public import Formalism.MahlerMeasure.MahlerMeasureProofs.SSDirect

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiAddLeft
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

def OrthLat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (D : ℤ),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) →
    ∃ (n₁ : ℕ) (e : Fin n₁ → MvPolynomial σ ℚ_[p]), (∀ a, e a ∈ L) ∧ LinearIndependent ℤ_[p] e ∧
      (∀ a b, a ≠ b → B (e a) (e b) = 0) ∧ (∀ a, B (e a) (e a) ≠ 0 ∧ (B (e a) (e a)).valuation ≤ D) ∧
      n₁ ≤ Module.finrank ℤ_[p] L ∧ Module.finrank ℤ_[p] L ≤ n₁ + Formalism.GM.M.bad p B L D

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestSymm : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    ∀ u ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2,
      ∀ v ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2,
        bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 u v =
          bePhi X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 v u

def RestLjjFin : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    (Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2).FG ∧
    ∃ W : Submodule ℚ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop 0 x.1).T.t) ℚ_[X.p]),
      FiniteDimensional ℚ_[X.p] W ∧ ∀ u ∈ Ljj X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2, u ∈ W

section Lin

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem bePhi_add_left (j : Fin G.T.t → ℕ) (jp : ℕ) (u u' v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (u + u') v = bePhi p (r := r) G j jp u v + bePhi p (r := r) G j jp u' v := by
  have hs := bePhi_sum_left p (r := r) G j jp (Finset.univ : Finset (Fin 2)) ![u, u'] v
  simpa [Fin.sum_univ_two] using hs

end Lin

variable {C0 CE1 CE2 X}

theorem restOrth_of (CM : ℝ) (hp2 : X.p ≠ 2) (hO : OrthLat) (hS : RestSymm C0 CE1 CE2 X)
    (hF : RestLjjFin C0 CE1 CE2 X) : RestOrth C0 CE1 CE2 X CM := by
  intro dl hdl aTop ha x hx
  obtain ⟨hfg, W, hW, hLW⟩ := hF dl hdl aTop ha x hx
  exact hO X.p _ _ _ W _ hp2 hW hLW hfg
    (fun c u v => bePhi_smul_left _ _ _ _ c u v)
    (fun u u' v => bePhi_add_left _ _ _ _ u u' v)
    (hS dl hdl aTop ha x hx)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankLjjSpan
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section Lvl

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem Ljj_span_fd (j : Fin G.T.t → ℕ) (jp : ℕ) :
    FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  haveI : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  haveI : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
  let bY := Module.finBasis ℚ_[p] Yq
  let Ms := xiMons (r := r) G (G.B - jp)
  let fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
    fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1
  let W := Submodule.span ℚ_[p] (Set.range fam)
  have hle : Ljj p (r := r) G j jp ≤ W.restrictScalars ℤ_[p] := by
    unfold Ljj
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, g, hg, rfl⟩
    have hyY : y ∈ Yq := (Submodule.mem_inf.1 hy).1
    have hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
      have h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq) := Submodule.mem_top
      rw [← bY.span_eq] at h3
      have h4 := Submodule.mem_map_of_mem (f := Yq.subtype) h3
      rw [Submodule.map_span, ← Set.range_comp] at h4
      exact h4
    have hg2 := xi_mem_span p G (G.B - jp) g hg
    show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W
    have hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p]
        (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
      have := Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) :
        MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2
      rw [Submodule.map_span, ← Set.range_comp] at this
      exact this
    have hmul := Submodule.mul_mem_mul hy3 hg2
    rw [Submodule.span_mul_span] at hmul
    refine Submodule.span_mono ?_ hmul
    rintro _ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨(a, ⟨m, hm⟩), rfl⟩
  haveI : FiniteDimensional ℚ_[p] W := FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam)
  have hle2 : Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) ≤ W := by
    rw [Submodule.span_le]
    intro x hx
    exact hle hx
  exact Submodule.finiteDimensional_of_le hle2

theorem finrank_Ljj_span (j : Fin G.T.t → ℕ) (jp : ℕ) :
    Module.finrank ℤ_[p] (Ljj p (r := r) G j jp) =
      Module.finrank ℚ_[p] (Submodule.span ℚ_[p] (Ljj p (r := r) G j jp : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) :=
  finrank_eq_span_gen (R := ℤ_[p]) (K := ℚ_[p]) _

end Lvl

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SumFinrankLeOfIndep
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestSumSpan
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestLvlDim : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b → ∀ x ∈ lv C0 CE1 CE2 X aTop b,
      rL C0 CE1 CE2 X aTop b x ≤
        Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2))

def RestSumSpan : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∑ x ∈ lv C0 CE1 CE2 X aTop b,
          Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2)) ≤
        Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p]
          (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
            Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
              Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])))

variable {C0 CE1 CE2 X}

theorem restDirQ_of (h1 : RestLvlDim C0 CE1 CE2 X) (h2 : RestSumSpan C0 CE1 CE2 X) : RestDirQ C0 CE1 CE2 X :=
  fun aTop hT aPlus hP b hk =>
    (Finset.sum_le_sum fun x hx => h1 aTop hT aPlus hP b hk x hx).trans (h2 aTop hT aPlus hP b hk)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem sum_finrank_le_of_indep {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V] [DecidableEq ι]
    (f : ι → Submodule K V) (hf : iSupIndep f) (T : Submodule K V) [FiniteDimensional K T] (s : Finset ι)
    (hle : ∀ i ∈ s, f i ≤ T) : ∑ i ∈ s, Module.finrank K (f i) ≤ Module.finrank K T := by
  have key : ∀ s : Finset ι, (∀ i ∈ s, f i ≤ T) →
      (⨆ i ∈ s, f i) ≤ T ∧ ∑ i ∈ s, Module.finrank K (f i) = Module.finrank K (⨆ i ∈ s, f i : Submodule K V) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      have h0 : (⨆ i ∈ (∅ : Finset ι), f i) = ⊥ := le_bot_iff.1 (iSup₂_le fun i hi => by simp at hi)
      rw [h0, finrank_bot, Finset.sum_empty]
      exact ⟨bot_le, rfl⟩
    | insert a s ha ih =>
      intro h
      obtain ⟨h1, h2⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hfa : f a ≤ T := h a (Finset.mem_insert_self a s)
      have e : (⨆ i ∈ insert a s, f i) = f a ⊔ ⨆ i ∈ s, f i := by
        rw [Finset.iSup_insert]
      haveI : FiniteDimensional K (f a) := Submodule.finiteDimensional_of_le hfa
      haveI : FiniteDimensional K (⨆ i ∈ s, f i : Submodule K V) := Submodule.finiteDimensional_of_le h1
      have hd : Disjoint (f a) (⨆ i ∈ s, f i) := hf.disjoint_biSup ha
      refine ⟨by rw [e]; exact sup_le hfa h1, ?_⟩
      rw [Finset.sum_insert ha, h2, e]
      have := Submodule.finrank_sup_add_finrank_inf_eq (f a) (⨆ i ∈ s, f i)
      rw [hd.eq_bot, finrank_bot, add_zero] at this
      omega
  obtain ⟨h1, h2⟩ := key s hle
  rw [h2]
  exact Submodule.finrank_mono h1

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem span_SSZ_fin (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) :
    FiniteDimensional ℚ_[X.p] (Submodule.span ℚ_[X.p]
      (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
        Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
          Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p]))) := by
  set Dd := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hDd
  set V0 := Submodule.span ℚ_[X.p]
    (((gmB Dd).SSZ X.p (r := X.r) : Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :
      Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) with hV0
  set W := Submodule.span (KK X.O) ((Dd.SSZ X.O (r := X.r) : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) :
      Set (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) with hW
  show FiniteDimensional ℚ_[X.p] V0
  haveI : FiniteDimensional (KK X.O) W := span_SSZ_finite Dd
  have hmemW : ∀ x ∈ V0, MvPolynomial.map (iotaX X) x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact map_SSZ (ι := iotaX X) (iotaX_int X) Dd x hx
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul_Q]; exact W.smul_mem _ hx
  refine Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt (rank_le (n := Module.finrank (KK X.O) W) fun s hs => ?_)
    (Cardinal.natCast_lt_aleph0))
  have hli : LinearIndependent ℚ_[X.p] (fun i : s => ((i : V0) : MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :=
    hs.map' V0.subtype (Submodule.ker_subtype V0)
  have hli2 := li_map (iotaX X) _ hli
  let w : s → W := fun i => ⟨MvPolynomial.map (iotaX X) (i : V0).1, hmemW _ (i : V0).2⟩
  have hli3 : LinearIndependent (KK X.O) w := LinearIndependent.of_comp W.subtype hli2
  have h := hli3.fintype_card_le_finrank
  simpa using h

theorem sum_gens_le (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N) (hB : G.BlockOK)
    (hr : 1 ≤ r) (s : Finset ((Fin G.T.t → ℕ) × ℕ)) (hs : ∀ x ∈ s, G.LevelOK x.1 x.2)
    [FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] ((G.SSZ p (r := r) :
      Submodule ℤ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])))] :
    ∑ x ∈ s, Module.finrank ℚ_[p] (Submodule.span ℚ_[p] (G.gens p (r := r) x.1 x.2)) ≤
      Module.finrank ℚ_[p] (Submodule.span ℚ_[p] ((G.SSZ p (r := r) :
        Submodule ℤ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))) := by
  classical
  have hind := (Formalism.GM.semisimple_direct_sum p N r G hB hr).1
  let g : {x // x ∈ s} → {ij : (Fin G.T.t → ℕ) × ℕ // G.LevelOK ij.1 ij.2} := fun y => ⟨y.1, hs y.1 y.2⟩
  have hg : Function.Injective g := fun y y' h => by
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have hind' := iSupIndep.comp hind hg
  rw [← Finset.sum_attach]
  refine sum_finrank_le_of_indep _ hind' _ s.attach fun y _ => ?_
  apply Submodule.span_le.2
  intro z hz
  apply Submodule.subset_span
  show z ∈ ((G.SSZ p (r := r) : Submodule ℤ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])) :
    Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]))
  unfold Formalism.GM.M.BlockData.SSZ
  exact Submodule.subset_span (Set.mem_iUnion.2 ⟨y.1.1, Set.mem_iUnion.2 ⟨y.1.2, Set.mem_iUnion.2 ⟨hs y.1 y.2, hz⟩⟩⟩)

theorem restSumSpan_proved : RestSumSpan C0 CE1 CE2 X := by
  classical
  intro aTop _ aPlus _ b _
  haveI := span_SSZ_fin C0 CE1 CE2 X aTop aPlus b
  have hr : 1 ≤ X.r := Nat.pos_of_ne_zero X.hm
  refine sum_gens_le X.p (gB C0 CE1 CE2 X aTop aPlus b) (gB_blockOK C0 CE1 CE2 X aTop aPlus b) hr
    (lv C0 CE1 CE2 X aTop b) (fun x hx => ?_)
  rw [lv_eq C0 CE1 CE2 X aTop aPlus b] at hx
  unfold levels at hx
  exact (Finset.mem_filter.1 hx).2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
