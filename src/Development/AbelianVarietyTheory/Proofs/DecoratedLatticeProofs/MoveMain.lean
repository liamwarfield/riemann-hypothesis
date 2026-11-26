module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainScalar

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeEqOfSplitPlaceFrameSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeEqOfSplitPlaceFrameSpan
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SplitFrameLat

open GlobalTheory.FinPl (latV idAt intAt)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mem_intAt (q : GlobalTheory.FinPl.SplitPt D k) : q.e ∈ intAt D (· = q.v) := by
  refine ⟨GlobalTheory.FrameGlob.e_mem_idAt q, ?_⟩
  have h1 : q.sec 1 = q.e := by
    have := q.sec_pr 1
    rwa [map_one, mul_one] at this
  have h := (q.int_iff 1).1 (one_mem _)
  rwa [h1] at h

theorem smul_mem_latV {V : HSp D} {L : GlobalTheory.FinPl.Lat V} (hL : Submodule.IsLattice D.host.E L) {v : GlobalTheory.FinPl.Pl D}
    {z : Fin V.rank → AE D} (hz : z ∈ latV V L (· = v)) {a : AE D} (ha : a ∈ intAt D (· = v)) :
    a • z ∈ latV V L (· = v) :=
  ((((GlobalTheory.FinPl.localComponents D (· = v)).2 V).2.2.2 L z hL).1 hz).2 v rfl a ha

theorem sec_pr_mul (q : GlobalTheory.FinPl.SplitPt D k) (a : AE D) (c : k) : q.sec (q.pr a * c) = a * q.sec c := by
  calc q.sec (q.pr a * c) = q.sec (q.pr (a * q.sec c)) := by rw [RingHom.map_mul q.pr, q.pr_sec]
    _ = q.e * (a * q.sec c) := q.sec_pr _
    _ = a * q.sec c := by rw [mul_left_comm, ← GlobalTheory.FrameGlob.sec_eq_mul]

theorem sec_int_iff (q : GlobalTheory.FinPl.SplitPt D k) (c : k) :
    toEAf D (q.sec c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ c ∈ 𝒪[k] := by
  have h := q.pr_mem_iff (q.sec c)
  rw [q.pr_sec, ← map_mul, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem sec_mem_iff (V : HSp D) (t : GA D V) (Λ L : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D))
    (q : GlobalTheory.FinPl.SplitPt D k) (M : Matrix (Fin V.rank) (Fin V.rank) k)
    (hβ : Formalism.L2.DIV.IsFrame β Λ) (hm : GlobalTheory.FinPl.Moves V t Λ L (· = q.v)) (hM : MovedTo (ofSplit q) V t β M)
    (x : Fin V.rank → k) :
    (fun i => q.sec ((M *ᵥ x) i)) ∈ latV V L (· = q.v) ↔ ∀ i, x i ∈ 𝒪[k] := by
  obtain ⟨b, hb⟩ : ∃ b : Matrix (Fin V.rank) (Fin V.rank) (AE D), b.map (toEAf D) = β.val := by
    choose f hf using fun s : Lev.EAf D => GlobalTheory.ResLoc.toEAf_surj (D := D) s
    exact ⟨β.val.map f, by ext i j; simp [hf]⟩
  set s : Fin V.rank → AE D := fun i => q.sec (x i) with hsdef
  have hs : ∀ i, s i ∈ idAt D (· = q.v) := fun i => GlobalTheory.FrameGlob.sec_mem_idAt q _
  have hy : ∀ i, (b *ᵥ s) i ∈ idAt D (· = q.v) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hs j)
  have hkey : (fun i => q.sec ((M *ᵥ x) i)) = Formalism.L2.Theta.mt V t *ᵥ (b *ᵥ s) := by
    rw [Matrix.mulVec_mulVec, ← hM b hb]
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact sec_pr_mul q _ _
  rw [hkey, ← hm _ hy]
  have hbridge : b *ᵥ s ∈ latV V Λ (· = q.v) ↔
      (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((b *ᵥ s) i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    ⟨GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ _, GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy⟩
  rw [hbridge, hβ]
  have h2 : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D ((b *ᵥ s) i))) = β.val *ᵥ fun i => toEAf D (s i) := by
    funext i
    change toEAf D ((b *ᵥ s) i) = _
    rw [← hb]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum (toEAf D)]
    simp only [RingHom.map_mul]
  rw [h2, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact forall_congr' fun i => sec_int_iff q (x i)

end GlobalTheory.SplitFrameLat

namespace GlobalTheory.SplitFrameLat

open GlobalTheory.FinPl (latV idAt intAt)

theorem latV_eq : ∀ {D : D7} (V : HSp D) (t : GA D V) (Λ L N : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) (σ : Fin V.rank ≃ Y), t ∈ GfC V → IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V t Λ L (· = q.v) → MovedTo (ofSplit q) V t β (F.β.submatrix id σ) → IntIn q V F N → GlobalTheory.FinPl.latV V L (· = q.v) = GlobalTheory.FinPl.latV V N (· = q.v) := by
  intro D V t Λ L N β k _ _ _ _ q Y _ _ F σ ht hΛ hβ hL hN hm hM hI
  have he := e_mem_intAt q

  have hw : ∀ z : Fin V.rank → AE D, q.e • z ∈ latV V L (· = q.v) ↔ q.e • z ∈ latV V N (· = q.v) := by
    intro z
    set y : Fin V.rank → k := fun i => q.pr (z i) with hydef
    have hz : q.e • z = fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ y)) i) := by
      rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
      funext i
      simp only [hydef, q.sec_pr, Pi.smul_apply, smul_eq_mul]
    have hL' := sec_mem_iff V t Λ L β q (F.β.submatrix id σ) hβ hm hM ((F.γ *ᵥ y) ∘ σ)
    rw [Matrix.submatrix_mulVec_equiv] at hL'
    have e1 : ((F.γ *ᵥ y) ∘ σ) ∘ σ.symm = F.γ *ᵥ y := by
      funext i; simp
    rw [e1] at hL'
    rw [hz, ← hI]
    have e2 : (fun i => q.sec (((F.β *ᵥ (F.γ *ᵥ y)) ∘ id) i)) = fun i => q.sec ((F.β *ᵥ (F.γ *ᵥ y)) i) := rfl
    rw [e2] at hL'
    rw [hL']
    exact ⟨fun h i => by simpa using h (σ.symm i), fun h i => h (σ i)⟩

  have hce : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, q.split.1]
  have hherm : ∀ y x : Fin V.rank → AE D,
      GlobalTheory.IwaPlace.hermAt V (cA D q.e • y) x = GlobalTheory.IwaPlace.hermAt V (cA D q.e • y) (q.e • x) := by
    intro y x
    unfold GlobalTheory.IwaPlace.hermAt
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    linear_combination (-(cA D (x i) * gA V i j * y j)) * hce
  have hbar : ∀ A B : GlobalTheory.FinPl.Lat V, IsSelfDualC V A → IsSelfDualC V B →
      (∀ z, q.e • z ∈ latV V B (· = q.v) → q.e • z ∈ latV V A (· = q.v)) →
      ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ idAt D (· = q.v)) →
        cA D q.e • z ∈ latV V A (· = q.v) → cA D q.e • z ∈ latV V B (· = q.v) := by
    intro A B hA hB hBA z hz h
    have hz' : ∀ i, (cA D q.e • z) i ∈ idAt D (· = q.v) := fun i => Ideal.mul_mem_left _ _ (hz i)
    refine ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V B q.v hB).2.2 _ hz').2 fun x hx => ?_
    rw [hherm]
    have hex : q.e • x ∈ latV V A (· = q.v) := hBA x (smul_mem_latV hB.1 hx he)
    exact ((GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V A q.v hA).2.2 _ hz').1 h _ hex
  have hsplit : ∀ z : Fin V.rank → AE D, (∀ i, z i ∈ idAt D (· = q.v)) → q.e • z + cA D q.e • z = z := by
    intro z hz
    obtain ⟨ε, hε, hs⟩ := q.above
    rw [← add_smul, hs]
    funext i
    exact ((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D q.v ε hε).1 (z i)).1 (hz i)
  have hgen : ∀ A B : GlobalTheory.FinPl.Lat V, IsSelfDualC V A → IsSelfDualC V B →
      (∀ z, q.e • z ∈ latV V A (· = q.v) ↔ q.e • z ∈ latV V B (· = q.v)) →
      latV V A (· = q.v) ≤ latV V B (· = q.v) := by
    intro A B hA hB hAB z hz
    have hs := GlobalTheory.FinPl.FrameLat.latV_supp hz
    have h1 : q.e • z ∈ latV V A (· = q.v) := smul_mem_latV hA.1 hz he
    have h3 : cA D q.e • z = z - q.e • z := by
      rw [eq_sub_iff_add_eq']
      exact hsplit z hs
    have h2 : cA D q.e • z ∈ latV V A (· = q.v) := by
      rw [h3]
      exact sub_mem hz h1
    have := add_mem ((hAB z).1 h1) (hbar A B hA hB (fun z => (hAB z).2) z hs h2)
    rwa [hsplit z hs] at this
  exact le_antisymm (hgen L N hL hN hw) (hgen N L hN hL fun z => (hw z).symm)

end GlobalTheory.SplitFrameLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeEqOfSplitPlaceFrameSpanStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_eq_of_splitPlace_frame_span : ∀ {D : D7} (V : HSp D) (t : GA D V) (Λ L N : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) (σ : Fin V.rank ≃ Y), t ∈ GfC V → IsSelfDualC V Λ → Formalism.L2.DIV.IsFrame β Λ → IsSelfDualC V L → IsSelfDualC V N → GlobalTheory.FinPl.Moves V t Λ L (· = q.v) → MovedTo (ofSplit q) V t β (F.β.submatrix id σ) → IntIn q V F N → GlobalTheory.FinPl.latV V L (· = q.v) = GlobalTheory.FinPl.latV V N (· = q.v) := by
  first | exact @GlobalTheory.SplitFrameLat.latV_eq | exact GlobalTheory.SplitFrameLat.latV_eq | (intros; apply GlobalTheory.SplitFrameLat.latV_eq <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RLatMove

theorem card_eq_of_frame {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) : Fintype.card Y = n := by
  apply le_antisymm
  · calc Fintype.card Y = (1 : Matrix Y Y k).rank := Matrix.rank_one.symm
      _ = (F.γ * F.β).rank := by rw [F.γβ]
      _ ≤ F.γ.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin n) := Matrix.rank_le_card_width _
      _ = n := Fintype.card_fin n
  · calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
      _ = (1 : Matrix (Fin n) (Fin n) k).rank := Matrix.rank_one.symm
      _ = (F.β * F.γ).rank := by rw [F.βγ]
      _ ≤ F.β.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card Y := Matrix.rank_le_card_width _

def frameGL {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) (B : GL Y k) (σ : Fin n ≃ Y) : GL (Fin n) k where
  val := (F.β * B.val).submatrix id σ
  inv := ((B⁻¹).val * F.γ).submatrix σ id
  val_inv := by
    rw [Matrix.submatrix_mul_equiv (F.β * B.val) ((B⁻¹).val * F.γ) id σ id]
    have : F.β * B.val * ((B⁻¹).val * F.γ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc B.val, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mul, F.βγ]
    rw [this, Matrix.submatrix_id_id]
  inv_val := by
    have h := Matrix.submatrix_mul_equiv ((B⁻¹).val * F.γ) (F.β * B.val) σ (Equiv.refl (Fin n)) σ
    simp only [Equiv.coe_refl] at h
    rw [h]
    have : (B⁻¹).val * F.γ * (F.β * B.val) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one]
    rw [this, Matrix.submatrix_one_equiv]

theorem frameGL_val {k : Type} [Field k] {n : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k n Y) (B : GL Y k) (σ : Fin n ≃ Y) :
    (frameGL F B σ).val = (F.β * B.val).submatrix id σ := rfl

end GlobalTheory.RLatMove

namespace GlobalTheory.RLatMove

theorem finJ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (hW : PkHyp W) : Finite {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := by
  haveI := hW.fin
  have : {PP | PP ∈ (pk W).Pg ∨ QAll W PP} = ((pk W).Pg : Set _) ∪ ⋃ t, ((pk W).Q t : Set _) := by
    ext PP; simp [QAll]
  have hf : Set.Finite {PP | PP ∈ (pk W).Pg ∨ QAll W PP} := by
    rw [this]; exact (Finset.finite_toSet _).union (Set.finite_iUnion fun t => Finset.finite_toSet _)
  exact hf.to_subtype

end GlobalTheory.RLatMove

namespace GlobalTheory.RLatMove

theorem move_main : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N j)) → ∃ b : ∀ j, GA D (Yc D j), (∀ j, b j ∈ GfC (Yc D j)) ∧ (∀ j, j < D.R.m → ∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) → GlobalTheory.FinPl.Moves (Yc D j) (b j) ((pk W).ΛY j) (N j) P) ∧ ∀ PP h j c (hc : j + c = (l PP h).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (l PP h).q) (Yc D j) (b j) ((pk W).βY j) (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hz hτ hNT hζ hLT hgP htP hdisj hPre hOrth hbas FY N hN hInt
  classical
  haveI : Finite {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := finJ W hW
  letI : Fintype {PP // PP ∈ (pk W).Pg ∨ QAll W PP} := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP} => (l i.1 i.2).q.v) := by
    intro i i' hii
    apply GlobalTheory.T.level_places_under_injective W hW
    simp only at hii
    rwa [(l i.1 i.2).under, (l i'.1 i'.2).under] at hii
  have key : ∀ j, j < D.R.m → ∃ t ∈ GfC (Yc D j),
      (∀ P : GlobalTheory.FinPl.Pl D → Prop, (∀ p, P p → p ∉ v.gP) →
        GlobalTheory.FinPl.Moves (Yc D j) t ((pk W).ΛY j) (N j) P) ∧
      ∀ PP h c (hc : j + c = (l PP h).s + 1),
        ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
          GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧
          MovedTo (ofSplit (l PP h).q) (Yc D j) t ((pk W).βY j)
            (((FY PP h j c hc).β * (bas PP h j c hc).val).submatrix id
              fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
    intro j hj
    have hsj : ∀ PP h, j + ((l PP h).s + 1 - j) = (l PP h).s + 1 := fun PP h => by
      have := (l PP h).hs; omega
    have hE : ∀ PP h, ∃ e : Ix (Fin D.R.k ⊕ Fin ((l PP h).s + 1)) (Fin D.R.t) j ≃ Fin (Yc D j).rank,
        GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e := by
      intro PP h
      obtain ⟨eqv, heqv⟩ := GlobalTheory.SymBridge.PhiAgreeProof.zPos_equiv D.R.k ((l PP h).s + 1) D.R.t j
      have hcard := card_eq_of_frame (FY PP h j _ (hsj PP h))
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod] at hcard
      have hr : D.R.k + ((l PP h).s + 1) + j * D.R.t = (Yc D j).rank := by
        rw [← hcard]; have := hsj PP h; omega
      exact ⟨eqv.trans (finCongr hr), fun x => by simp [heqv]⟩
    choose E hEo using hE
    let σ : ∀ PP h, Fin (Yc D j).rank ≃ (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((l PP h).s + 1 - j)) :=
      fun PP h => (E PP h).symm.trans (stdOrd (Fin D.R.k) (Fin D.R.t) j _ (hsj PP h))
    let M : ∀ i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP}, GL (Fin (Yc D j).rank) (l i.1 i.2).k :=
      fun i => frameGL (FY i.1 i.2 j _ (hsj i.1 i.2)) (bas i.1 i.2 j _ (hsj i.1 i.2)) (σ i.1 i.2)
    have hsd := GlobalTheory.T.self_dual_lattice_frame_chain W hW j hj
    obtain ⟨t, ht, Lt, hLt, hMv, hAgree, hMT⟩ := GlobalTheory.T.exists_base_point_carrying_lattice_and_frames D (Yc D j) ((pk W).ΛY j) (N j) ((pk W).βY j)
      hsd.1 (hN j hj) {PP // PP ∈ (pk W).Pg ∨ QAll W PP} (fun i => (l i.1 i.2).k)
      (fun i => (l i.1 i.2).q) hinj M
    refine ⟨t, ht, ?_, ?_⟩
    · intro P hP
      have hloc : ∀ w, P w → GlobalTheory.FinPl.latV (Yc D j) Lt (· = w) = GlobalTheory.FinPl.latV (Yc D j) (N j) (· = w) := by
        intro w hw
        by_cases hex : ∃ i : {PP // PP ∈ (pk W).Pg ∨ QAll W PP}, (l i.1 i.2).q.v = w
        · obtain ⟨⟨PP, h⟩, rfl⟩ := hex
          have hPg : PP ∉ (pk W).Pg := fun hPg => hP _ hw ((hgP _).2 ⟨PP, hPg, (l PP h).under⟩)
          have hb := hbas PP h hPg j _ (hsj PP h)
          have hm := hMT ⟨PP, h⟩
          have hval : (M ⟨PP, h⟩).val = (FY PP h j _ (hsj PP h)).β.submatrix id (σ PP h) := by
            simp only [M, frameGL_val, hb, Units.val_one, Matrix.mul_one]
          rw [hval] at hm
          exact GlobalTheory.T.selfDual_lattice_eq_of_splitPlace_frame_span (Yc D j) t ((pk W).ΛY j) Lt (N j) ((pk W).βY j) _ (l PP h).q _
            (FY PP h j _ (hsj PP h)) (σ PP h) ht hsd.1 hsd.2 hLt (hN j hj) (hMv _) hm
            (hInt PP h j _ (hsj PP h))
        · push_neg at hex
          exact hAgree w (fun i => (hex i).symm)
      have hEq := GlobalTheory.T.latticeCompletion_eq_of_local_agreement (Yc D j) Lt (N j) P hLt.1 (hN j hj).1 hloc
      have := hMv P
      unfold GlobalTheory.FinPl.Moves at this ⊢
      rwa [← hEq]
    · intro PP h c hc
      obtain rfl : c = (l PP h).s + 1 - j := by omega
      exact ⟨E PP h, hEo PP h, hMT ⟨PP, h⟩⟩
  choose T hT hMovesT hFrT using key
  refine ⟨fun j => if h : j < D.R.m then T j h else 1, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j < D.R.m
    · simp only [dif_pos h]; exact hT j h
    · simp only [dif_neg h]; exact one_mem _
  · intro j hj P hP
    simp only [dif_pos hj]
    exact hMovesT j hj P hP
  · intro PP h j c hc
    have hj : j < D.R.m := by have := (l PP h).hs; omega
    simp only [dif_pos hj]
    exact hFrT j hj PP h c hc

end GlobalTheory.RLatMove
