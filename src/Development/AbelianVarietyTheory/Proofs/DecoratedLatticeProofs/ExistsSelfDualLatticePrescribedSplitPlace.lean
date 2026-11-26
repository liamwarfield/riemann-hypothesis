module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesHarishChandraModuleAdmissible

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePrescribedSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePrescribedSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def place (q : SplitPt D k) : GlobalTheory.LocMod.Place D k where
  e := q.e
  split := q.split
  π := q.pr
  ι := q.sec
  π_ι := q.pr_sec
  ι_π := q.sec_pr
  cont_π := q.cont_pr
  cont_ι := q.cont_sec

theorem suppAt_one (e : AE D) (S : HSp D) : SuppAt e S 1 := by
  intro i j
  simp [Formalism.L2.Theta.mt]

theorem isLoc_one (q : SplitPt D k) {S : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) : (place q).IsLoc F 1 1 := by
  refine ⟨suppAt_one _ _, ?_⟩
  simp [Formalism.L2.Theta.mt, F.βγ, place]

theorem locGrp (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) :
    (∀ gk : GL Y k, ∃! g, (place q).IsLoc F g gk) ∧ (∀ g, SuppAt (place q).e S g → ∃ gk, (place q).IsLoc F g gk) ∧
      ∀ g gk h hk, (place q).IsLoc F g gk → (place q).IsLoc F h hk → (place q).IsLoc F (g * h) (gk * hk) :=
  (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k (place q)).1 S Y F

def frameOf (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y]
    (F : GlobalTheory.LocMod.Frame k S.rank Y) : Frame q S Y where
  b := F.β
  b' := F.γ
  bb' := F.βγ
  b'b := F.γβ
  gl :=
    { toFun := fun g => ((locGrp q S Y F).1 g).exists.choose
      map_one' := ((locGrp q S Y F).1 1).unique ((locGrp q S Y F).1 1).exists.choose_spec (isLoc_one q F)
      map_mul' := fun g g' => ((locGrp q S Y F).1 (g * g')).unique ((locGrp q S Y F).1 (g * g')).exists.choose_spec
        ((locGrp q S Y F).2.2 _ _ _ _ ((locGrp q S Y F).1 g).exists.choose_spec
          ((locGrp q S Y F).1 g').exists.choose_spec) }
  gl_supp g := ((locGrp q S Y F).1 g).exists.choose_spec.1
  gl_mat g := ((locGrp q S Y F).1 g).exists.choose_spec.2

def stdLat (k : Type) [Field k] [ValuativeRel k] (Y : Type) : Submodule 𝒪[k] (Y → k) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)

theorem mem_std {Y : Type} (y : Y → k) : y ∈ stdLat k Y ↔ ∀ i, y i ∈ 𝒪[k] := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  exact forall_congr' fun i => ⟨fun ⟨c, hc⟩ => hc ▸ c.2, fun h => ⟨⟨y i, h⟩, rfl⟩⟩

theorem std_eq_span (Y : Type) [Fintype Y] [DecidableEq Y] :
    stdLat k Y = Submodule.span 𝒪[k] (Set.range fun i : Y => (Pi.single i 1 : Y → k)) := by
  apply le_antisymm
  · intro x hx
    have hx' := (mem_std x).1 hx
    have : x = ∑ i, (⟨x i, hx' i⟩ : 𝒪[k]) • (Pi.single i 1 : Y → k) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine (mem_std _).2 fun i => ?_
    show (Pi.single j (1 : k) : Y → k) i ∈ 𝒪[k]
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem isLattice_std (Y : Type) [Fintype Y] [DecidableEq Y] : Submodule.IsFullLattice k (stdLat k Y) := by
  refine { toIsLattice := ?_, span_eq_top := ?_ }
  · apply Submodule.IsLattice.of_fg k
    rw [std_eq_span]
    exact Submodule.fg_span (Set.finite_range _)
  · apply eq_top_iff.mpr
    rw [← (Pi.basisFun k Y).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine (mem_std _).2 fun j => ?_
    rw [Pi.basisFun_apply, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 h2 ⟨w.1, fun hw => w.2 (hPQ _ hw)⟩

theorem latV_le_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) ≤ latV S L' (· = v) := by
  intro y hy
  obtain ⟨⟨ε, -, -, hεint, hεat, -⟩, hSv⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)
  have hyv := ((hSv S).2.2.2 L y hL).1 hy
  have hoff := ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· ≠ v₀)).2 S).2.2.2
  have hy₀ : y ∈ latV S L (· ≠ v₀) := by
    rw [hoff L y hL]
    refine ⟨fun i => idAt_mono (fun w hw => hw ▸ hv) (hyv.1 i), fun u _ e he => ?_⟩
    by_cases huv : u = v
    · subst huv
      exact hyv.2 u rfl e he
    · obtain ⟨⟨εu, -, -, -, hεuat, hεuoff⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = u)
      have hz : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = u) :=
          (Submodule.mem_iInf _).2 fun w =>
            (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (hyv.1 i)).2 ⟨w.1, fun hw => huv (w.2.symm.trans hw)⟩
        change e * y i = 0
        rw [← (hεuat e).1 he.1, mul_comm εu e, mul_assoc, (hεuoff (y i)).1 hyi, mul_zero]
      rw [hz]
      exact zero_mem _
  rw [h] at hy₀
  have h2 := ((hoff L' y hL').1 hy₀).2 v hv ε hεint
  have hεy : ε • y = y := funext fun i => (hεat (y i)).1 (hyv.1 i)
  rwa [hεy] at h2

theorem exists_selfDual_frame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (L₀ : Lat S), IsSelfDualC S L₀ → ∃ L : Lat S, IsSelfDualC S L ∧ (∀ v, v ≠ q.v → latV S L (· = v) = latV S L₀ (· = v)) ∧ ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ latV S L (· = q.v) := by
  intro D k _ _ _ _ q S Y _ _ F L₀ hL₀
  obtain ⟨M, hM, hMΛ, hoff⟩ :=
    GlobalTheory.T.exists_selfDual_lattice_with_prescribed_splitComponent D k q S Y (frameOf q S Y F) L₀ (stdLat k Y) hL₀ (isLattice_std Y)
  refine ⟨M, hM, fun v hv => le_antisymm (latV_le_of_off hM.1 hL₀.1 hv hoff)
    (latV_le_of_off hL₀.1 hM.1 hv hoff.symm), fun y => ?_⟩
  exact (mem_std y).symm.trans (hMΛ y)

end GlobalTheory.SplitLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePrescribedSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDualLattice_prescribed_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (L₀ : Lat S), IsSelfDualC S L₀ → ∃ L : Lat S, IsSelfDualC S L ∧ (∀ v, v ≠ q.v → latV S L (· = v) = latV S L₀ (· = v)) ∧ ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ latV S L (· = q.v) := by
  first | exact @GlobalTheory.SplitLat.exists_selfDual_frame | exact GlobalTheory.SplitLat.exists_selfDual_frame | (intros; apply GlobalTheory.SplitLat.exists_selfDual_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSelfDualLatticeSplitPlaceDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSelfDualLatticeSplitPlaceDecomposition
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitSelfDual

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def intMat : AddSubgroup (Matrix Y Y' k) where
  carrier := {x | ∀ r q, x r q ∈ 𝒪[k]}
  add_mem' hx hy r q := add_mem (hx r q) (hy r q)
  zero_mem' _ _ := zero_mem _
  neg_mem' hx r q := neg_mem (hx r q)

theorem isHalf_neg {S T : HSp D} {e : AE D} {y : WO S T} (h : IsHalf e y) : IsHalf e (-y) := fun i j => by
  rw [Matrix.neg_apply, mul_neg, h i j]

theorem symplO_neg_right (S T : HSp D) (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  rw [← GlobalTheory.LatVac.symplHom_apply, map_neg]; rfl

theorem psi_neg_eq_one {ψ : AddChar (AF D.host.F) ℂ} {a : AF D.host.F} (h : ψ a = 1) : ψ (-a) = 1 := by
  have := AddChar.map_add_eq_mul ψ a (-a)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, one_mul] at this
  exact this.symm

theorem eq_zero_of_halves {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {y : WO S T} (h1 : IsHalf e y)
    (h2 : IsHalf (cA D e) y) : y = 0 := by
  ext i j
  rw [Matrix.zero_apply, ← h1 i j, ← h2 i j, ← mul_assoc, he.2.1, zero_mul]

def dualHalf (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (FS : Frame k S.rank Y')
    (FT : Frame k T.rank Y) : AddSubgroup (WO S T) where
  carrier := {y | IsHalf (cA D p.e) y ∧
    ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) y) = 1}
  add_mem' {a b} ha hb := ⟨GlobalTheory.SplitScalar.isHalf_add ha.1 hb.1, fun t ht => by
    rw [GlobalTheory.LatVac.symplO_add_right, AddChar.map_add_eq_mul, ha.2 t ht, hb.2 t ht, one_mul]⟩
  zero_mem' := ⟨GlobalTheory.SplitScalar.isHalf_zero _, fun t _ => by
    rw [GlobalTheory.SplitScalar.symplO_zero_right, AddChar.map_zero_eq_one]⟩
  neg_mem' {a} ha := ⟨isHalf_neg ha.1, fun t ht => by
    rw [symplO_neg_right]; exact psi_neg_eq_one (ha.2 t ht)⟩

def lat (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (FS : Frame k S.rank Y')
    (FT : Frame k T.rank Y) : AddSubgroup (WO S T) :=
  (intMat (k := k) (Y := Y) (Y' := Y')).map (Witness.upH p FS FT) ⊔ dualHalf p ψ S T FS FT

section
variable (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y)

theorem mem_lat {u : WO S T} : u ∈ lat p ψ S T FS FT ↔
    ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ ∃ y ∈ dualHalf p ψ S T FS FT, p.up FS FT x + y = u := by
  unfold lat
  rw [AddSubgroup.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, y, hy, h⟩
    exact ⟨x, hx, y, hy, h⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨_, ⟨x, hx, rfl⟩, y, hy, h⟩

theorem up_mem_lat {x : Matrix Y Y' k} (hx : ∀ r q, x r q ∈ 𝒪[k]) : p.up FS FT x ∈ lat p ψ S T FS FT :=
  (mem_lat p ψ FS FT).2 ⟨x, hx, 0, zero_mem _, add_zero _⟩

theorem dualHalf_le_lat : dualHalf p ψ S T FS FT ≤ lat p ψ S T FS FT := le_sup_right

theorem half_e_of_mem {u : WO S T} (hu : u ∈ lat p ψ S T FS FT) (he : IsHalf p.e u) :
    ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ u = p.up FS FT x := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_lat p ψ FS FT).1 hu
  have hye : IsHalf p.e y := (Witness.half_add (Witness.up_half p FS FT x)).1 (by rwa [add_comm] at he)
  rw [eq_zero_of_halves p.split hye hy.1, add_zero]
  exact ⟨x, hx, rfl⟩

theorem half_c_of_mem {u : WO S T} (hu : u ∈ lat p ψ S T FS FT) (hc : IsHalf (cA D p.e) u) :
    u ∈ dualHalf p ψ S T FS FT := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_lat p ψ FS FT).1 hu
  have hxc : IsHalf (cA D p.e) (p.up FS FT x) := (Witness.half_add hy.1).1 hc
  rw [eq_zero_of_halves p.split (Witness.up_half p FS FT x) hxc, zero_add]
  exact hy

end

theorem selfDual_lattice_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), ∃ Λ : AddSubgroup (WO S T), (∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1) ∧ (∀ y, IsHalf p.e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D p.e) l ∧ ψ (symplO S T l y) ≠ 1) ∧ (∀ y, IsHalf (cA D p.e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf p.e l ∧ ψ (symplO S T l y) ≠ 1) ∧ (∀ x : Matrix Y Y' k, p.up FS FT x ∈ Λ ↔ ∀ r q, x r q ∈ 𝒪[k]) ∧ (∀ u ∈ Λ, IsHalf p.e u → ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ u = p.up FS FT x) ∧ (∀ u ∈ Λ, IsHalf (cA D p.e) u → ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) u) = 1) := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT
  obtain ⟨⟨ψk, hψk⟩, hcont, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hψc, hψ1⟩ := hcont ψk hψk
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψk hψc hψ1
  obtain ⟨-, -, hiso, hpsi, hpair⟩ := GlobalTheory.LocSympl.halves_at_split D k p Y Y' S T FS FT ψ ψk hψk
  have hconj : IsSplitIdem D (cA D p.e) := GlobalTheory.SplitScalar.isSplitIdem_conj p.split
  refine ⟨lat p ψ S T FS FT, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro u hu u' hu'
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_lat p ψ FS FT).1 hu
    obtain ⟨x', hx', y', hy', rfl⟩ := (mem_lat p ψ FS FT).1 hu'
    have h4 : symplO S T y y' = 0 := GlobalTheory.SplitScalar.half_orth hconj hy.1 hy'.1
    have h3 : ψ (symplO S T y (p.up FS FT x')) = 1 := by
      rw [GlobalTheory.SplitScalar.symplO_skew]; exact psi_neg_eq_one (hy.2 x' hx')
    rw [GlobalTheory.LatVac.symplO_add_left, GlobalTheory.LatVac.symplO_add_right, GlobalTheory.LatVac.symplO_add_right, hiso, h4,
      zero_add, add_zero, AddChar.map_add_eq_mul, hy'.2 x hx, h3, one_mul]
  ·
    intro y hy hyΛ
    have hyx : p.up FS FT (p.down FS FT y) = y := Witness.up_down p FS FT hy
    have hx : ¬ ∀ r q, p.down FS FT y r q ∈ 𝒪[k] := fun hx => hyΛ (hyx ▸ up_mem_lat p ψ FS FT hx)
    push_neg at hx
    obtain ⟨r, q, hrq⟩ := hx
    set a := p.down FS FT y r q with ha
    have hrq' : ¬ valuation k a ≤ 1 := fun h => hrq ((Valuation.mem_integer_iff _ _).2 h)
    have ha0 : a ≠ 0 := by rintro h; rw [h, map_zero] at hrq'; exact hrq' zero_le'
    have hc0 : 0 < valuation k (c : k) := by simp [zero_lt_iff]
    have hcv : ¬ valuation k (c * a) ≤ valuation k (c : k) := by
      rw [map_mul]; intro h
      have h' : valuation k (c : k) * valuation k a ≤ valuation k (c : k) * 1 := by rwa [mul_one]
      exact hrq' ((mul_le_mul_iff_of_pos_left hc0).1 h')
    obtain ⟨z, hz, hzne⟩ : ∃ z, valuation k z ≤ valuation k (c * a) ∧ ψk z ≠ 1 := by
      by_contra hcon; push_neg at hcon; exact hcv ((hc _).1 hcon)
    have hsum : ∀ t : Matrix Y Y' k, ∑ r', ∑ q', Matrix.single r q (z / a) r' q' * t r' q' = z / a * t r q := by
      intro t; simp [Matrix.single_apply, ite_and]
    obtain ⟨y', hy'c, hy'p⟩ := hpair (Matrix.single r q (z / a))
    have hy'Λ : y' ∈ dualHalf p ψ S T FS FT := by
      refine ⟨hy'c, fun t ht => ?_⟩
      rw [hpsi t y' hy'c, hy'p, hsum]
      have ha0' : 0 < valuation k a := by simp [zero_lt_iff, ha0]
      have hv : valuation k (z / a * t r q) ≤ valuation k (c : k) := by
        rw [map_mul, map_div₀]
        calc valuation k z / valuation k a * valuation k (t r q) ≤ valuation k z / valuation k a * 1 := by
              gcongr; exact (Valuation.mem_integer_iff _ _).1 (ht r q)
          _ ≤ valuation k (c : k) := by rw [mul_one, div_le_iff₀ ha0', ← map_mul]; exact hz
      rw [(hc c).2 le_rfl _ hv, Circle.coe_one]
    refine ⟨y', dualHalf_le_lat p ψ FS FT hy'Λ, hy'c, GlobalTheory.SplitScalar.psi_skew_ne ?_⟩
    rw [← hyx, hpsi _ y' hy'c, hy'p, hsum, ← ha, div_mul_cancel₀ z ha0]
    exact fun h => hzne (Circle.ext (by rw [h, Circle.coe_one]))
  ·
    intro y hy hyΛ
    have hyd : y ∉ dualHalf p ψ S T FS FT := fun h => hyΛ (dualHalf_le_lat p ψ FS FT h)
    have : ¬ ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) y) = 1 :=
      fun h => hyd ⟨hy, h⟩
    push_neg at this
    obtain ⟨t, ht, hne⟩ := this
    exact ⟨p.up FS FT t, up_mem_lat p ψ FS FT ht, Witness.up_half p FS FT t, hne⟩
  ·
    intro x
    refine ⟨fun hx => ?_, fun hx => up_mem_lat p ψ FS FT hx⟩
    obtain ⟨x', hx', hxx⟩ := half_e_of_mem p ψ FS FT hx (Witness.up_half p FS FT x)
    have := congrArg (p.down FS FT) hxx
    rw [Witness.down_up, Witness.down_up] at this
    exact this ▸ hx'
  · intro u hu he
    exact half_e_of_mem p ψ FS FT hu he
  · intro u hu hc' t ht
    exact (half_c_of_mem p ψ FS FT hu hc').2 t ht

end GlobalTheory.SplitSelfDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSelfDualLatticeSplitPlaceDecompositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localSelfDualLattice_split_place_decomposition : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), ∃ Λ : AddSubgroup (WO S T), (∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1) ∧ (∀ y, IsHalf p.e y → y ∉ Λ → ∃ l ∈ Λ, IsHalf (cA D p.e) l ∧ ψ (symplO S T l y) ≠ 1) ∧ (∀ y, IsHalf (cA D p.e) y → y ∉ Λ → ∃ l ∈ Λ, IsHalf p.e l ∧ ψ (symplO S T l y) ≠ 1) ∧ (∀ x : Matrix Y Y' k, p.up FS FT x ∈ Λ ↔ ∀ r q, x r q ∈ 𝒪[k]) ∧ (∀ u ∈ Λ, IsHalf p.e u → ∃ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) ∧ u = p.up FS FT x) ∧ (∀ u ∈ Λ, IsHalf (cA D p.e) u → ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT t) u) = 1) := by
  first | exact @GlobalTheory.SplitSelfDual.selfDual_lattice_split | exact GlobalTheory.SplitSelfDual.selfDual_lattice_split | (intros; apply GlobalTheory.SplitSelfDual.selfDual_lattice_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointHeckeComponentTameAndResidual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointHeckeComponentTameAndResidual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt)

section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem sec_one' : q.sec 1 = q.e := by
  have := q.sec_pr 1
  rwa [map_one, mul_one] at this

theorem sec_mul' (x y : k) : q.sec x * q.sec y = q.sec (x * y) := by
  have h := q.sec_pr (q.sec x * q.sec y)
  rw [map_mul, q.pr_sec, q.pr_sec, ← mul_assoc, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem idlU_mul (x y : k) (h : x * y = 1) : (q.sec x + (1 - q.e)) * (q.sec y + (1 - q.e)) = 1 := by
  have h1 := sec_mul' q x y
  rw [h, sec_one'] at h1
  have h2 := GlobalTheory.FrameGlob.sec_eq_mul q x
  have h3 := GlobalTheory.FrameGlob.sec_eq_mul q y
  have h4 := q.split.1
  linear_combination h1 + h2 + h3 + h4

def idlU (x : kˣ) : (AE D)ˣ :=
  ⟨q.sec x + (1 - q.e), q.sec (x⁻¹ : kˣ) + (1 - q.e), idlU_mul q _ _ x.mul_inv, idlU_mul q _ _ x.inv_mul⟩

theorem continuous_idlU : Continuous (idlU q) :=
  Units.continuous_iff.2 ⟨(q.cont_sec.comp Units.continuous_val).add continuous_const,
    (q.cont_sec.comp Units.continuous_coe_inv).add continuous_const⟩

theorem res_eq_locK {PP : Formalism.L2.DIV.Pl D.host.E} {H : Formalism.L2.Host.HChar D.host.E}
    {c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} (hr : Formalism.IndefR.Links.IsRes H PP c) {a : D.host.E} (ha : IntAt PP a)
    (ha0 : a ≠ 0) (r : (Formalism.L2.DIV.kP PP)ˣ) (hra : (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a) :
    c r = H.locK PP (Units.mk0 a ha0) := by
  obtain ⟨r₀, s, hs, e⟩ := ha
  have hs0 : (algebraMap (𝓞 D.host.E) D.host.E s) ≠ 0 :=
    RingOfIntegers.coe_ne_zero_iff.2 (by rintro rfl; exact hs (zero_mem _))
  haveI := PP.isMaximal
  letI := Ideal.Quotient.field PP.asIdeal
  have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hsp := Formalism.L2.Col.reduction_spec PP hs e
  have h1 := hr s (Units.mk0 _ hs0) (Units.mk0 _ hu) rfl rfl
  have h2 := hr r₀ (Units.mk0 _ hs0 * Units.mk0 _ ha0) (Units.mk0 _ hu * r) (by simp [e])
    (by simp [hra, hsp])
  rw [map_mul, map_mul, h1] at h2
  exact mul_left_cancel h2

end Place
end GlobalTheory.LocMod.SplitHecke

namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt)
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

theorem chi_idlU_rat {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) {χ : (AE D)ˣ →* Circle}
    {H : Formalism.L2.Host.HChar D.host.E} (hχ : Formalism.IndefR.Links.ChrEq χ H) {a : D.host.E} (ha0 : a ≠ 0) (u : kˣ)
    (hu : (u : k) = (ofSplit q).pr a) : (χ (idlU q u) : ℂ) = H.locK PP (Units.mk0 a ha0) := by
  exact hχ.2 PP q.e ⟨h.1.1, by
      obtain ⟨ε, hε, hs⟩ := q.above
      exact ⟨q.v, ε, hε, Or.inl ⟨h.1.2.1, hs⟩⟩, h.2⟩ (Units.mk0 _ ha0) (idlU q u) (by
        change q.sec u + (1 - q.e) = 1 + q.e * (incA D a - 1)
        rw [hu]
        change q.sec (q.pr _) + _ = _
        rw [q.sec_pr]
        ring)

end GlobalTheory.LocMod.SplitHecke

namespace GlobalTheory.LocMod.SplitHecke
open GlobalTheory.FinPl (SplitPt)
open Formalism.L2.NTheta (IsIdemAt)
open _root_.Formalism.L2.Col (IntAt)
section Place
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k)

def prOU : 𝓞 D.host.E →+* k := (q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)

theorem prOU_lt {PP : Formalism.L2.DIV.Pl D.host.E} (h : IsIdemAt q.e PP) (z : 𝓞 D.host.E) :
    z ∈ PP.asIdeal ↔ valuation k (prOU q z) < 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h0 : prOU q z ≠ 0 := (map_ne_zero (q.pr.comp (incA D))).2 (RingOfIntegers.coe_ne_zero_iff.2 hz)
  rw [h.2 z hz, ← q.sec_pr, ← q.int_iff]
  change (q.pr.comp (incA D)) _ ∉ _ ↔ _
  rw [map_inv₀, Valuation.mem_integer_iff, map_inv₀, not_le]
  exact one_lt_inv₀ (a := valuation k (prOU q z)) (zero_lt_iff.2 ((map_ne_zero _).2 h0))

theorem prOU_le {PP : Formalism.L2.DIV.Pl D.host.E} (hi : ∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ IntAt PP x)
    (z : 𝓞 D.host.E) : valuation k (prOU q z) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).1 ((hi _).2
    ⟨z, 1, (Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top, by simp⟩)

end Place

theorem tame_and_res : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → DenseRange (ofSplit q).pr → ∀ (χ : (AE D)ˣ →* Circle) (H : Formalism.L2.Host.HChar D.host.E) (c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (μ : kˣ →* ℂˣ), ChrEq χ H → IsRes H PP c → (ofSplit q).IsComp χ μ → IsTame μ ∧ ∀ (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), Formalism.L2.Col.IntAt PP a → (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a → (u : k) = (ofSplit q).pr a → μ u = c r := by
  intro D k _ _ _ _ q PP h hi hd χ H c μ hχ hr hμ
  have comp : ∀ x : kˣ, (μ x : ℂ) = χ (idlU q x) := fun x => hμ x (idlU q x) rfl
  have val : ∀ (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), IntAt PP a →
      (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a → (u : k) = (ofSplit q).pr a → μ u = c r := by
    intro a u r ha hra hu
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact u.ne_zero (hu.trans (q.pr.comp (incA D)).map_zero)
    apply Units.ext
    rw [comp u, chi_idlU_rat q h hχ ha0 u hu, res_eq_locK hr ha ha0 r hra]
  refine ⟨?_, val⟩
  have rat : ∀ (a : D.host.E) (y : kˣ), (y : k) = (ofSplit q).pr a → valuation k ((y : k) - 1) < 1 →
      χ (idlU q y) = 1 := by
    intro a y hy hy1
    have hv : valuation k (y : k) = 1 := by simpa using Valuation.map_one_add_of_lt (valuation k) hy1
    have ha : IntAt PP a := (hi a).1 (by rw [← hy, Valuation.mem_integer_iff, hv])
    have hred : Formalism.L2.Col.redP PP a = 1 := by
      obtain ⟨r₀, s, hs, e⟩ := ha
      have hsp := Formalism.L2.Col.reduction_spec PP hs e
      have e' : prOU q s * y = prOU q r₀ := by
        rw [hy]
        exact ((q.pr.comp (incA D)).map_mul _ _).symm.trans (congrArg (q.pr.comp (incA D)) e)
      have hrs : r₀ - s ∈ PP.asIdeal := by
        rw [prOU_lt q h, map_sub, ← e', ← mul_sub_one, map_mul]
        calc valuation k (prOU q s) * valuation k ((y : k) - 1) ≤ 1 * valuation k ((y : k) - 1) :=
              by gcongr; exact prOU_le q hi s
          _ < 1 := by rwa [one_mul]
      haveI := PP.isMaximal
      letI := Ideal.Quotient.field PP.asIdeal
      have hu : Ideal.Quotient.mk PP.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      have e2 : Ideal.Quotient.mk PP.asIdeal r₀ = Ideal.Quotient.mk PP.asIdeal s :=
        Ideal.Quotient.eq.2 hrs
      rw [e2] at hsp
      exact mul_left_cancel₀ hu (hsp.trans (mul_one _).symm)
    have h1 := val a y 1 ha (by rw [Units.val_one, hred]) hy
    rw [map_one] at h1
    have h2 := comp y
    rw [h1, Units.val_one] at h2
    exact Circle.coe_injective h2.symm
  intro x hx
  suffices hs : χ (idlU q x) = 1 by
    apply Units.ext
    rw [comp x, hs]
    simp
  by_contra hne
  have hc : Continuous fun y => χ (idlU q y) := hχ.1.1.comp (continuous_idlU q)
  have h1 : {y : kˣ | χ (idlU q y) ≠ 1} ∈ nhds x := (isOpen_ne_fun hc continuous_const).mem_nhds hne
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at h1
  obtain ⟨W, hW, hW'⟩ := h1
  have h2 : {y : k | valuation k (y - x) < 1} ∈ nhds (x : k) := by
    rw [IsValuativeTopology.mem_nhds_iff']
    exact ⟨1, by simp⟩
  obtain ⟨a, ha1, ha2, ha3⟩ := hd.mem_nhds (Filter.inter_mem hW (Filter.inter_mem h2 (isOpen_ne.mem_nhds x.ne_zero)))
  refine hW' (a := Units.mk0 _ ha3) ha1 (rat a _ rfl ?_)
  have := Valuation.map_add_lt (valuation k) ha2 hx
  simpa using this

end GlobalTheory.LocMod.SplitHecke
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointHeckeComponentTameAndResidualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPoint_heckeComponent_tame_and_residual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → DenseRange (ofSplit q).pr → ∀ (χ : (AE D)ˣ →* Circle) (H : Formalism.L2.Host.HChar D.host.E) (c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (μ : kˣ →* ℂˣ), ChrEq χ H → IsRes H PP c → (ofSplit q).IsComp χ μ → IsTame μ ∧ ∀ (a : D.host.E) (u : kˣ) (r : (Formalism.L2.DIV.kP PP)ˣ), Formalism.L2.Col.IntAt PP a → (r : Formalism.L2.DIV.kP PP) = Formalism.L2.Col.redP PP a → (u : k) = (ofSplit q).pr a → μ u = c r := by
  first | exact @GlobalTheory.LocMod.SplitHecke.tame_and_res | exact GlobalTheory.LocMod.SplitHecke.tame_and_res | (intros; apply GlobalTheory.LocMod.SplitHecke.tame_and_res <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSlice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSlice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_mul (x : k) (b : AE D) : p.ι x * b = p.ι (x * p.π b) := by
  have h : p.ι (x * p.π b) = p.e * (p.ι x * b) := by
    calc p.ι (x * p.π b) = p.ι (p.π (p.ι x) * p.π b) := by rw [p.π_ι]
      _ = p.ι (p.π (p.ι x * b)) := by rw [p.π.map_mul]
      _ = p.e * (p.ι x * b) := p.ι_π _
  rw [h, ← mul_assoc, GlobalTheory.LocMod.Witness.e_ι]

theorem map_ι_mul {a b c : Type} [Fintype b] (M : Matrix a b k) (N : Matrix b c (AE D)) :
    M.map p.ι * N = (M * N.map p.π).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem frame_card {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) : Fintype.card Y = N := by
  have e : (Y → k) ≃ₗ[k] (Fin N → k) := LinearEquiv.ofLinearMap (Matrix.toLin' F.β) (Matrix.toLin' F.γ)
    (by rw [← Matrix.toLin'_mul, F.βγ, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, F.γβ, Matrix.toLin'_one])
  simpa using e.finrank_eq

def splitCols (n n' : Type) : Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × Matrix n Unit k where
  toFun x := (x.toCols₁, x.toCols₂)
  invFun q := fromCols q.1 q.2
  left_inv x := fromCols_toCols x
  right_inv q := by simp
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)
    · exact continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inr j)
  continuous_invFun := by
    refine continuous_matrix fun i j => ?_
    cases j with
    | inl a => exact continuous_fst.matrix_elem i a
    | inr u => exact continuous_snd.matrix_elem i u

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def box (Ξ : SB (Matrix n n' k)) : SB (Matrix n Unit k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun c := comapH (splitCols n n') (prodSB Ξ c)
  map_add' c c' := Subtype.ext (funext fun x => by simp [splitCols, mul_add])
  map_smul' a c := Subtype.ext (funext fun x => by simp [splitCols]; ring)

theorem box_apply (Ξ : SB (Matrix n n' k)) (c : SB (Matrix n Unit k)) (x : Matrix n (n' ⊕ Unit) k) :
    (box Ξ c).1 x = Ξ.1 x.toCols₁ * c.1 x.toCols₂ := rfl

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem heis_slice {S A L T : HSp D} (d : OrthDec S A L) (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ)
    (u : WO A T) (w v : WO L T) :
    heisO ψ S T ((d.resS T).symm (0, v)) f ((d.resS T).symm (u, w)) =
      heisO ψ L T v (fun w => f ((d.resS T).symm (u, w))) w := by
  simp only [heisO]
  rw [d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, zero_add,
    ← map_add, Prod.mk_add_mk, add_zero]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem isHalf_slice {S A L T : HSp D} (d : OrthDec S A L) {a : AE D} {y : WO L T} (hy : IsHalf a y) :
    IsHalf a ((d.resS T).symm (0, y)) := by
  intro i j
  rw [resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, hy i l]

variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem beta_eq (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) :
    F₀.β = fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β) (B.o.iB.map (p.π.comp (incA D)) * FL.β) := by
  ext r (a | u)
  · exact h.1 r a
  · cases u
    rw [h.2 r, fromCols_apply_inr, Matrix.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [vecB, Matrix.mulVec, dotProduct, Place.pr, map_sum, map_mul, Matrix.map_apply, hL, RingHom.comp_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
variable {ρ : ℕ} {B : BesLev D ρ} {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} {FL : Frame k B.L.rank Unit}

theorem rat_map_π {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) : (rat M).map p.π = M.map (p.π.comp (incA D)) := rfl

theorem up_fromCols (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (x : Matrix n Unit k) :
    p.up F₀ FS (fromCols 0 x) = (B.o.resS S).symm (0, p.up FL FS x) := by
  have k1 : x * FL.γ * B.o.qB.map (p.π.comp (incA D)) * F₀.β = fromCols (0 : Matrix n n' k) x := by
    rw [beta_eq p h hL, Matrix.mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.o.qB.map _) (B.o.iA.map _), ← Matrix.map_mul, B.o.qB_iA,
      ← Matrix.mul_assoc (B.o.qB.map _) (B.o.iB.map _), ← Matrix.map_mul, B.o.qB_iB]
    simp [FL.γβ]
  have k2 : fromCols (0 : Matrix n n' k) x * F₀.γ = x * FL.γ * B.o.qB.map (p.π.comp (incA D)) := by
    rw [← k1, Matrix.mul_assoc (x * FL.γ * B.o.qB.map (p.π.comp (incA D))) F₀.β F₀.γ, F₀.βγ, Matrix.mul_one]
  rw [resS_symm_apply, Matrix.zero_mul, zero_add]
  unfold Place.up
  rw [pB, map_ι_mul, rat_map_π]
  congr 1
  rw [Matrix.mul_assoc FS.β (fromCols 0 x) F₀.γ, k2]
  simp only [Matrix.mul_assoc]

theorem resS_up_snd (h : p.IsCoreFrame B s FA F₀) (hL : ∀ r, FL.β r () = s * p.pr (B.ζ r)) {S : HSp D}
    (FS : Frame k S.rank n) (t : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS t)).2 = p.up FL FS t.toCols₂ := by
  have k1 : t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) * FL.β = t.toCols₂ := by
    calc t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) * FL.β
        = ((t * F₀.γ) * fromCols (B.o.iA.map (p.π.comp (incA D)) * FA.β)
            (B.o.iB.map (p.π.comp (incA D)) * FL.β)).toCols₂ := by
          rw [Matrix.mul_fromCols, toCols₂_fromCols, Matrix.mul_assoc (t * F₀.γ)]
      _ = ((t * F₀.γ) * F₀.β).toCols₂ := by rw [← beta_eq p h hL]
      _ = t.toCols₂ := by rw [Matrix.mul_assoc, F₀.γβ, Matrix.mul_one]
  have k2 : t * F₀.γ * B.o.iB.map (p.π.comp (incA D)) = t.toCols₂ * FL.γ := by
    rw [← k1, Matrix.mul_assoc (t * F₀.γ * B.o.iB.map (p.π.comp (incA D))) FL.β FL.γ, FL.βγ, Matrix.mul_one]
  rw [resS_apply]
  dsimp only
  unfold Place.up
  rw [jB, map_ι_mul, rat_map_π]
  simp only [Matrix.mul_assoc] at k2 ⊢
  rw [k2]

end GlobalTheory.SliceLine

namespace GlobalTheory.SliceLine

open GlobalTheory.MixModel.OrthDec GlobalTheory.LocFlat.CFac

theorem toCols_add {k n n' : Type} [Field k] (t : Matrix n (n' ⊕ Unit) k) (x : Matrix n Unit k) :
    (t + fromCols (0 : Matrix n n' k) x).toCols₁ = t.toCols₁ ∧ (t + fromCols (0 : Matrix n n' k) x).toCols₂ = t.toCols₂ + x :=
  ⟨by ext i j; simp, by ext i j; simp⟩

theorem slice_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∃ FL : Frame k B.L.rank Unit, (∀ r, FL.β r () = s * p.pr (B.ζ r)) ∧ ∀ (Ξ : SB (Matrix n n' k)) (u₀ : WO B.A S), ∃ T', p.IsModel ψ FL FS T' ∧ ∀ (c : SB (Matrix n Unit k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ w, T' c w = T₀ Ψ ((B.o.resS S).symm (u₀, w)) := by
  intro D k _ _ _ _ p ψ ρ B S s n n' _ _ _ _ FA F₀ FS h T₀ hT
  have hA := frame_card FA
  have h0 := frame_card F₀
  have hr := B.o.rank_add
  rw [Fintype.card_sum, Fintype.card_unit] at h0
  have hL1 : B.L.rank = 1 := by omega
  have hsub : ∀ r r' : Fin B.L.rank, r = r' := fun r r' => Fin.ext (by have := r.isLt; have := r'.isLt; omega)
  have hv : ∀ r, s * p.pr (B.ζ r) ≠ 0 := by
    intro r₀ h₀
    have hz : ∀ r, s * p.pr (B.ζ r) = 0 := fun r => by rw [hsub r r₀]; exact h₀
    have hcol : ∀ r, F₀.β r (Sum.inr ()) = 0 := by
      intro r
      rw [h.2 r]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [vecB, Matrix.mulVec, dotProduct, Place.pr, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := hz j
      simp only [Place.pr] at this
      rw [mul_left_comm, this, mul_zero]
    have := congrFun (congrFun F₀.γβ (Sum.inr ())) (Sum.inr ())
    simp [Matrix.mul_apply, hcol] at this
  obtain ⟨FL, hFL⟩ : ∃ FL : Frame k B.L.rank Unit, ∀ r, FL.β r () = s * p.pr (B.ζ r) := by
    refine ⟨⟨Matrix.of fun r _ => s * p.pr (B.ζ r), Matrix.of fun _ r => (s * p.pr (B.ζ r))⁻¹, ?_, ?_⟩, fun r => rfl⟩
    · ext r r'
      obtain rfl := hsub r r'
      simp [Matrix.mul_apply]
      rw [← _root_.mul_inv_rev]
      exact mul_inv_cancel₀ (hv r)
    · ext u u'
      simp [Matrix.mul_apply]
      rw [Finset.sum_congr rfl (g := fun _ => (1 : k)) fun j _ => by rw [← _root_.mul_inv_rev]; exact inv_mul_cancel₀ (hv j)]
      simp [hL1]
  refine ⟨FL, hFL, fun Ξ u₀ => ?_⟩
  let T' : SB (Matrix n Unit k) →ₗ[ℂ] (WO B.L S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun w : WO B.L S => (B.o.resS S).symm (u₀, w))).comp (T₀.comp (box Ξ))
  have hT' : ∀ c w, T' c w = T₀ (box Ξ c) ((B.o.resS S).symm (u₀, w)) := fun _ _ => rfl
  refine ⟨T', ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun c Ψ hΨ w => ?_⟩
  · let f := T₀ (box Ξ Φ)
    have hf : IsThetaFunO ψ B.V₀ S f := hT.theta (box Ξ Φ)
    let e := (B.o.resS S).symm
    let incl : WO B.L S →+ WO B.V₀ S := sandwich (1 : Mx D S.rank S.rank) B.o.pB
    have he (v : WO B.L S) : incl v = e (0, v) := by
      rw [sandwich_apply, Matrix.one_mul, resS_symm_apply, Matrix.zero_mul, zero_add]
    have hadd (w v : WO B.L S) : e (u₀, w + v) = e (u₀, w) + incl v := by
      rw [he, ← map_add e, Prod.mk_add_mk, add_zero]
    have hslice : IsThetaFunO ψ B.L S (fun w => f (e (u₀, w))) := by
      refine ⟨?_, ?_, hf.cont.comp ((B.o.continuous_resS_symm S).comp
        (continuous_const.prodMk continuous_id)), ?_⟩
      · intro γ w
        have hrat : e (0, ratW S B.L γ) = ratW S B.V₀ (γ * B.o.qB) := by
          rw [resS_symm_apply, Matrix.zero_mul, zero_add, ratW_eq, ratW_eq, rat_mul]; rfl
        rw [add_comm (ratW S B.L γ) w, hadd, he, add_comm (e (u₀, w)), hrat, hf.quasi,
          ← hrat, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
          GlobalTheory.MixModel.symplOH_zero_left, zero_add]
      · obtain ⟨U, hU, hlevel⟩ := hf.level
        refine ⟨U.comap incl, hU.preimage (continuous_sandwich _ _), fun v hv hzero => ?_⟩
        funext w
        have h := congrFun (hlevel (incl v) hv (map_sandwich _ _ _ hzero)) (e (u₀, w))
        rw [he, heis_slice] at h
        exact h
      · intro m L hL hzero w
        simp only [hadd]
        exact hf.smooth m (incl.comp L) ((continuous_sandwich _ _).comp hL)
          (fun t => map_sandwich _ _ _ (hzero t)) _
    exact hslice
  · have e := hT.trans (fromCols 0 x) (box Ξ Φ) (box Ξ Φ') (fun t => by
      rw [box_apply, box_apply, hΦ, (toCols_add t x).1, (toCols_add t x).2])
    funext w
    rw [hT', e, up_fromCols p h hFL, heis_slice]
    rfl
  · have e := hT.modul ((B.o.resS S).symm (0, y)) (isHalf_slice B.o hy) (box Ξ Φ) (box Ξ Φ') (fun t => by
      simp only [box_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, resS_up_snd p h hFL, symplO_zero_right',
        zero_add]
      ring)
    funext w
    rw [hT', e, heis_slice]
    rfl
  · have e : Ψ = box Ξ c := Subtype.ext (funext fun x => by rw [hΨ, box_apply]; rfl)
    rw [hT', e]

end GlobalTheory.SliceLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelRestrictedToLineSliceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_model_restricted_to_line_slice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∃ FL : Frame k B.L.rank Unit, (∀ r, FL.β r () = s * p.pr (B.ζ r)) ∧ ∀ (Ξ : SB (Matrix n n' k)) (u₀ : WO B.A S), ∃ T', p.IsModel ψ FL FS T' ∧ ∀ (c : SB (Matrix n Unit k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ()))) → ∀ w, T' c w = T₀ Ψ ((B.o.resS S).symm (u₀, w)) := by
  first | exact @GlobalTheory.SliceLine.slice_line | exact GlobalTheory.SliceLine.slice_line | (intros; apply GlobalTheory.SliceLine.slice_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealData
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealData
open Formalism.BasicNotions

namespace GlobalTheory.TwArch

theorem archOnRecord_closed : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
    ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D :=
  fun hDS hHC D => GlobalTheory.ArchRec.archOnRecord hDS hHC D

end GlobalTheory.TwArch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealDataStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanThetaCorrespondence_towers_real_data : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ArchOnRecord D := by
  first | exact @GlobalTheory.TwArch.archOnRecord_closed | exact GlobalTheory.TwArch.archOnRecord_closed | (intros; apply GlobalTheory.TwArch.archOnRecord_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeZeroOfIsIdemAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.LevelPlaces

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7}

theorem splitAt_of {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D} {ε : AF D.host.F} (he : IsSplitIdem D e)
    (hε : IsPlaceIdem D v ε) (h : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitAt D v e := by
  obtain ⟨α, rfl, h3, h4⟩ := hε
  have : α = singleV D.host.F v 1 := af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [h3, evalV_singleV_same]
    · rw [h4 w hw, evalV_singleV_ne _ v _ hw]
  subst this
  exact ⟨he.1, he.2.1, h⟩

theorem ne_zero_of_isIdemAt {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt e P) : e ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  exact ((hP.2 x hx0).1 hx) (by rw [zero_mul, map_zero]; exact zero_mem _)

end GlobalTheory.LevelPlaces
end
end
