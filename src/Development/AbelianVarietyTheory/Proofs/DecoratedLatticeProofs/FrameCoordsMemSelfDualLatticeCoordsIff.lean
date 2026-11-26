module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulColMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameCoordsMemSelfDualLatticeCoordsIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LineSelfDual

theorem hT_frame (D : D7) (S : HSp D) (u v : S.V) :
    S.hT u v = ∑ i, ∑ j, star (S.frame.equivFun u i) * S.gram i j * S.frame.equivFun v j := by
  conv_lhs => rw [← S.frame.sum_repr u, ← S.frame.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Basis.equivFun_apply, Formalism.BasicNotions.HSpace.gram, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

noncomputable def selfDualLatticeCoordsInHermitianFrame (D : D7) (S : HSp D) : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
  S.L0.map (S.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap

theorem frameCoords_mem_selfDualLatticeCoords_iff (D : D7) (S : HSp D) (u : S.V) : S.frame.equivFun u ∈ selfDualLatticeCoordsInHermitianFrame D S ↔ u ∈ S.L0 :=
  ⟨fun ⟨z, hz, e⟩ => S.frame.equivFun.injective e ▸ hz, fun hu => ⟨u, hu, rfl⟩⟩

theorem isSelfDualC_selfDualLatticeCoordsInFrame (D : D7) (S : HSp D) : IsSelfDualC S (selfDualLatticeCoordsInHermitianFrame D S) := by
  refine ⟨⟨S.standardTuple_isLattice.fg.map _, ?_⟩, ?_⟩
  · exact fun _ _ => (LinearIndependent.iff_fractionRing (𝓞 D.host.E) D.host.E).mp
  · intro y
    obtain ⟨v, rfl⟩ := S.frame.equivFun.surjective y
    have h2 : v ∈ S.L0 ↔ ∀ u ∈ S.L0, S.hT u v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual S.hT S.L0 = S.L0 from S.baseLattice_isUnimodular]
      simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
    have h3 : ∀ z : D.host.E, z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ ∃ b : 𝓞 D.host.E, (b : D.host.E) = z :=
      fun z => Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ⟨a, ha⟩, fun ⟨a, ha⟩ => ⟨a, ha⟩⟩
    rw [frameCoords_mem_selfDualLatticeCoords_iff, h2]
    constructor
    · rintro H _ ⟨u, hu, rfl⟩
      have := (h3 _).1 (H u hu)
      rwa [hT_frame] at this
    · intro H u hu
      rw [h3, hT_frame]
      exact H _ ⟨u, hu, rfl⟩

end GlobalTheory.LineSelfDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalProperty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TraceAtG

theorem mat_embA_besFrame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {ρ : ℕ} (B : BesLev D ρ) (s : k) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)) (hF : p.IsBesFrame B s FA F) (h : GA D B.A)
    (g₀ : GL n k) (hh : (mt B.A h).map p.π = FA.β * g₀.val * FA.γ) :
    (mt B.V (embA B.d B.o h)).map p.π = F.β * (GlobalTheory.RootEx.embX c g₀).val * F.γ := by
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  have hint : (mt B.V (B.d.emb0 (B.o.emb (h, 1)))).map p.π * ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) =
      (rat (B.d.i₀ * B.o.iA)).map p.π * FA.β * g₀.val := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, eA, Matrix.map_mul, hh]
    simp only [Matrix.mul_assoc]
    rw [FA.γβ, Matrix.mul_one]
  refine GlobalTheory.LocGrp.eq_embX F _ g₀ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 hint fun j => ?_
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine GlobalTheory.LocGrp.fix_vec (GlobalTheory.LocGrp.map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact GlobalTheory.LocGrp.fix_col (GlobalTheory.LocGrp.map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

end GlobalTheory.TraceAtG

end

noncomputable section
open GlobalTheory.FamTrace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocComb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevPin
open GlobalTheory.FinPl (idAt MxAt grpAt SplitPt)

variable {D : D7}

theorem idAt_mono {P P' : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ w, P w → P' w) : idAt D P ≤ idAt D P' :=
  inf_le_inf_left _ (le_iInf fun w => iInf_le_of_le ⟨w.1, fun hw => w.2 (h _ hw)⟩ le_rfl)

theorem mxAt_of_half {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {m n : ℕ} (w : Mx D m n)
    (h : IsHalf (q.e + cA D q.e) w) : MxAt P w := by
  obtain ⟨ε, h1, h2⟩ := q.above
  obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 h1
  intro i j
  refine idAt_mono (fun w (hw : w = q.v) => hw ▸ hP) (GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_)
  rw [← h2]
  exact h i j

theorem exists_fold (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) {ι : Type} (c : ι → WO S T →₀ ℂ)
    (hc : ∀ i, ∀ w ∈ (c i).support, MxAt P w) (l : List ι) : ∃ c' : WO S T →₀ ℂ, (∀ w ∈ c'.support, MxAt P w) ∧
      ∀ f, comb ψ S T c' f = l.foldr (fun i f' => comb ψ S T (c i) f') f := by
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, fun w hw => ?_, fun f => ?_⟩
    · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hw)
      exact fun i j => zero_mem _
    · rw [comb, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul,
        GlobalTheory.MixPer.heisO_zero]
      rfl
  | cons i l ih =>
    obtain ⟨c', h1, h2⟩ := ih
    obtain ⟨c'', h3, h4⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 (c i) c'
    refine ⟨c'', fun w hw => ?_, fun f => by rw [h4, h2]; rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := h3 w hw
    exact fun a b => add_mem (hc i x hx a b) (h1 y hy a b)

theorem mxAt_cast {F : ℕ → HSp D} {T : HSp D} {P : GlobalTheory.FinPl.Pl D → Prop} {s j : ℕ} (h : s = j) (x : WO (F s) T →₀ ℂ)
    (hx : ∀ w ∈ x.support, MxAt P w) : ∀ w ∈ (cast (congrArg (fun n => WO (F n) T →₀ ℂ) h) x).support, MxAt P w := by
  subst h
  exact hx

def conjHom {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) :
    GL (Fin N) k →* GL Y k where
  toFun g := ⟨F.γ * g.val * F.β, F.γ * (g⁻¹).val * F.β, by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc g.val,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, F.γβ], by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul, ← Matrix.mul_assoc (g⁻¹).val,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, F.γβ]⟩
  map_one' := Units.ext (by
    change F.γ * (1 : Matrix (Fin N) (Fin N) k) * F.β = 1
    rw [Matrix.mul_one, F.γβ])
  map_mul' g h := Units.ext (by
    change F.γ * (g.val * h.val) * F.β = (F.γ * g.val * F.β) * (F.γ * h.val * F.β)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul])

theorem conj_iff {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y)
    (M : GL (Fin N) k) (x : GL Y k) : M.val = F.β * x.val * F.γ ↔ x = conjHom F M := by
  constructor
  · intro h
    refine Units.ext ?_
    change x.val = F.γ * M.val * F.β
    rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, F.γβ, Matrix.one_mul, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  · rintro rfl
    change M.val = F.β * (F.γ * M.val * F.β) * F.γ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, F.βγ, Matrix.one_mul, Matrix.mul_assoc, F.βγ, Matrix.mul_one]

def frameSub {G : Type} [Group G] {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (ρ : G →* GL (Fin N) k) (F : Frame k N Y) (J : Subgroup (GL Y k)) : Subgroup G :=
  J.comap ((conjHom F).comp ρ)

theorem mem_frameSub {G : Type} [Group G] {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]
    (ρ : G →* GL (Fin N) k) (F : Frame k N Y) (J : Subgroup (GL Y k)) (g : G) :
    g ∈ frameSub ρ F J ↔ ∀ x : GL Y k, (ρ g).val = F.β * x.val * F.γ → x ∈ J := by
  constructor
  · intro h x hx
    rw [(conj_iff F _ x).1 hx]
    exact h
  · intro h
    exact h _ ((conj_iff F _ _).2 rfl)

theorem under_inj {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (hT : GlobalTheory.Core.Mi.IsTypePlaces Pg) {PP PP' : Formalism.L2.DIV.Pl D.host.E}
    (h : PP ∈ Pg) (h' : PP' ∈ Pg) (e : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) : PP = PP' := by
  have hm : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    have := hT.1 PP h
    simpa [IsDedekindDomain.HeightOneSpectrum.under] using this
  obtain ⟨Q, _, hu⟩ := hT.2 _ hm
  exact (hu PP ⟨h, rfl⟩).trans (hu PP' ⟨h', e.symm⟩).symm

end GlobalTheory.LevPin

namespace GlobalTheory.LevPin

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem exists_locComb {a : XGeo D} {y : YRat a} {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E}
    (l : LocX a βT PP) (S : SymData l.k l.s D.R.k) {N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)} {β : ∀ j, GL (Fin (Yc D j).rank) (Lev.EAf D)}
    {b : ∀ j, GA D (Yc D j)} {bas : ∀ j c, j + c = l.s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) l.k}
    (Y : LocY l y N β b bas) (ν : Measure l.k) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    ∃ (eg : ∀ j, WO (Yc D j) (Yc D (j + 1)) →₀ ℂ) (egT : WO (Yc D (l.s + 1)) D.sp.X' →₀ ℂ)
      (cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ),
      (∀ j a' (H : j + a' = l.s), (ofSplit l.q).IsCombAt ψ (Y.FY j (a' + 1) (by omega)) (Y.FY (j + 1) a' (by omega)) (eg j)
        ((S.T (Fin D.R.t)).Phi j a' H)) ∧
      (ofSplit l.q).IsCombAt ψ (Y.FY (l.s + 1) 0 rfl) l.FT egT (S.T (Fin D.R.t)).PhiTop ∧
      (∀ j a' (H : j + 1 + a' = l.s), (ofSplit l.q).IsCombAt ψ (l.FX j (by omega)) (l.FX (j + 1) (by omega)) (cg j)
        ((S.T (Fin D.R.t)).entry S.ψ ν j a' H 1 1)) ∧
      (ofSplit l.q).IsCombAt ψ (l.FX l.s (by omega)) (l.FX (l.s + 1) le_rfl) (cg l.s)
        (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))) ∧
      (ofSplit l.q).IsCombAt ψ (l.FX (l.s + 1) le_rfl) l.FM (cg (l.s + 1))
        ((S.T (Fin D.R.t)).xiTop (box _ (1 : l.kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t)))) ∧
      (∀ j, ∀ w ∈ (eg j).support, IsHalf (l.q.e + cA D l.q.e) w) ∧ (∀ j, ∀ w ∈ (cg j).support, IsHalf (l.q.e + cA D l.q.e) w) := by
  have keyE : ∀ j, ∃ c : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ a' (H : j + a' = l.s),
      (ofSplit l.q).IsCombAt ψ (Y.FY j (a' + 1) (by omega)) (Y.FY (j + 1) a' (by omega)) c ((S.T (Fin D.R.t)).Phi j a' H)) ∧
      ∀ w ∈ c.support, IsHalf (l.q.e + cA D l.q.e) w := by
    intro j
    by_cases hj : j ≤ l.s
    · obtain ⟨c, hc⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (Y.FY j (l.s - j + 1) (by omega))
        (Y.FY (j + 1) (l.s - j) (by omega)) ((S.T (Fin D.R.t)).Phi j (l.s - j) (by omega))
      refine ⟨c, fun a' H => ?_, hc.1⟩
      obtain rfl : a' = l.s - j := by omega
      exact hc
    · exact ⟨0, fun a' H => by omega, by simp⟩
  choose eg heg sEg using keyE
  obtain ⟨egT, hegT⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (Y.FY (l.s + 1) 0 rfl) l.FT
    (S.T (Fin D.R.t)).PhiTop
  obtain ⟨c₁, h₁⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX l.s (by omega)) (l.FX (l.s + 1) le_rfl)
    (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t)))
  obtain ⟨c₂, h₂⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX (l.s + 1) le_rfl) l.FM
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : l.kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))
  have keyC : ∀ j, ∃ c : WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ,
      (∀ c' (H : j + 1 + c' = l.s), (ofSplit l.q).IsCombAt ψ (l.FX j (by omega)) (l.FX (j + 1) (by omega)) c
        ((S.T (Fin D.R.t)).entry S.ψ ν j c' H 1 1)) ∧ (j = l.s → HEq c c₁) ∧ (j = l.s + 1 → HEq c c₂) ∧
      ∀ w ∈ c.support, IsHalf (l.q.e + cA D l.q.e) w := by
    intro j
    by_cases hj : j < l.s
    · obtain ⟨c, hc⟩ := GlobalTheory.LocMod.CombAt.exists_isCombAt (ofSplit l.q) hψ (l.FX j (by omega)) (l.FX (j + 1) (by omega))
        ((S.T (Fin D.R.t)).entry S.ψ ν j (l.s - j - 1) (by omega) 1 1)
      refine ⟨c, fun c'' H' => ?_, fun h => by omega, fun h => by omega, hc.1⟩
      obtain rfl : c'' = l.s - j - 1 := by omega
      exact hc
    · by_cases h1 : j = l.s
      · subst h1
        exact ⟨c₁, fun c' H => by omega, fun _ => HEq.rfl, fun h => by omega, h₁.1⟩
      · by_cases h2 : j = l.s + 1
        · subst h2
          exact ⟨c₂, fun c' H => by omega, fun h => by omega, fun _ => HEq.rfl, h₂.1⟩
        · exact ⟨0, fun c' H => by omega, fun h => (h1 h).elim, fun h => (h2 h).elim, by simp⟩
  choose cg k1 k2 k3 k4 using keyC
  refine ⟨eg, egT, cg, heg, hegT, k1, ?_, ?_, sEg, k4⟩
  · rw [eq_of_heq (k2 l.s rfl)]; exact h₁
  · rw [eq_of_heq (k3 (l.s + 1) rfl)]; exact h₂

end GlobalTheory.LevPin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCharacterConductorOneExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCharacterConductorOneExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Topology

noncomputable section

namespace GlobalTheory.WeilCondUnif

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem splitPlace_polarisationDatum_inv_integral (p : SplitPt D k) (hU : p.UnitAA) : p.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := exists_idem p
  have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = p.v) := by
    refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
    · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · refine Ideal.mem_iInf.2 fun w => ?_
      change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  have := pr_int p (hU.1 _ hm).2.2
  rwa [map_mul, pr_pair_tmul p h, map_one, map_one, mul_one] at this

theorem hasConductor_of_mul {χ ψk : AddChar k Circle} {ξ : k} (hv : valuation k ξ = 1) (he : ∀ x, ψk x = χ (ξ * x))
    (h : HasConductor χ 1) : HasConductor ψk 1 := by
  intro x
  rw [← h x]
  have hξ0 : ξ ≠ 0 := fun h0 => by rw [h0, map_zero] at hv; exact zero_ne_one hv
  constructor
  · intro H y hy
    have := H (ξ⁻¹ * y) (by rw [map_mul, map_inv₀, hv, inv_one, one_mul]; exact hy)
    rwa [he, ← mul_assoc, mul_inv_cancel₀ hξ0, one_mul] at this
  · intro H y hy
    rw [he]
    exact H _ (by rw [map_mul, hv, one_mul]; exact hy)

theorem hasConductor_weil (q : SplitPt D k) (hU : q.UnitAA) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (ψk : AddChar k Circle) (h : (ofSplit q).IsChar ψ ψk) (hx : (ofSplit q).xi ≠ 0) : HasConductor ψk 1 := by
  have h' : ∀ x, (ψk x : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec x) := h
  set ξ : k := q.pr (incA D D.host.xi0) with hξ
  have hξ0 : ξ ≠ 0 := hx
  have hx0 : D.host.xi0 ≠ 0 := fun h0 => hξ0 (by rw [hξ, h0, map_zero, map_zero])
  have hinv : q.pr (incA D D.host.xi0⁻¹) = ξ⁻¹ := map_inv₀ (q.pr.comp (incA D)) D.host.xi0
  have h1 : valuation k ξ ≤ 1 := (Valuation.mem_integer_iff _ _).1 (xi_zero_projection_integral q hU)
  have h2 : valuation k ξ⁻¹ ≤ 1 := by rw [← hinv]; exact (Valuation.mem_integer_iff _ _).1 (splitPlace_polarisationDatum_inv_integral q hU)
  have hv : valuation k ξ = 1 := by
    have hp : valuation k ξ * valuation k ξ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hξ0, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ValueGroupWithZero k) = valuation k ξ * valuation k ξ⁻¹ := hp.symm
      _ ≤ valuation k ξ * 1 := mul_le_mul_right h2 _
      _ = valuation k ξ := mul_one _
  have hχ : q.IsChar ψ (ψk.mulShift ξ⁻¹) := fun a => by
    rw [AddChar.mulShift_apply, h', mul_comm ξ⁻¹ a, ← hinv, sec_mul_pr, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0,
      map_one, one_mul]
  refine hasConductor_of_mul hv (fun x => ?_) (hasConductor_one D k q ψ _ hψ hχ hU)
  rw [AddChar.mulShift_apply, ← mul_assoc, inv_mul_cancel₀ hξ0, one_mul]

theorem int_transfer {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : SplitPt D k) (q' : SplitPt D k') (he : q.e = q'.e) (z : AE D) : q.pr z ∈ 𝒪[k] ↔ q'.pr z ∈ 𝒪[k'] := by
  rw [q.int_iff, q'.int_iff, q.sec_pr, q'.sec_pr, he]

theorem dense_transfer {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : SplitPt D k) (q' : SplitPt D k') (he : q.e = q'.e) (hd : DenseRange (q'.pr.comp (incA D))) :
    DenseRange (q.pr.comp (incA D)) := by
  let f : k' → k := fun y => q.pr (q'.sec y)
  have hf : Continuous f := q.cont_pr.comp q'.cont_sec
  have hs : Function.Surjective f := fun a => ⟨q'.pr (q.sec a), by
    show q.pr (q'.sec (q'.pr (q.sec a))) = a
    rw [q'.sec_pr, ← he, e_mul_sec, q.pr_sec]⟩
  have hc : f ∘ (q'.pr.comp (incA D)) = q.pr.comp (incA D) := funext fun a => by
    show q.pr (q'.sec (q'.pr (incA D a))) = q.pr (incA D a)
    rw [q'.sec_pr, ← he, map_mul, pr_e, one_mul]
  have := hs.denseRange.comp hd hf
  rwa [hc] at this

end Local

section Unif

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {K : Type} [Field K] [NumberField K]

theorem lt_one_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem isUnif_of (P : HeightOneSpectrum (𝓞 K)) (ι : K →+* k) (hint : ∀ a, ι a ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P a)
    (hd : DenseRange ι) (hq : ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 K) ∉ P.asIdeal ^ 2) :
    ∃ ϖ : kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ (ϖ : k) = ι ((Formalism.L2.Col.qOf P : ℕ) : K) := by
  have hvN := GlobalTheory.AtTypeExists.valuation_norm P hq
  set N : K := ((Formalism.L2.Col.qOf P : ℕ) : K) with hN
  have hN0 : N ≠ 0 := fun h0 => WithZero.exp_ne_zero (hvN.symm.trans (by rw [h0, map_zero]))
  have hI : ∀ a, valuation k (ι a) ≤ 1 ↔ P.valuation K a ≤ 1 := fun a => by
    rw [← GlobalTheory.AtTypeExists.intAt_iff, ← hint, Valuation.mem_integer_iff]
  have hvN1 : P.valuation K N ≠ 0 := by rw [hvN]; exact WithZero.exp_ne_zero
  have K1 : ∀ a : K, valuation k (ι a) < 1 → valuation k (ι a) ≤ valuation k (ι N) := by
    intro a ha
    by_cases a0 : a = 0
    · rw [a0, map_zero, map_zero]; exact zero_le'
    have ha0 : valuation k (ι a) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]; exact (map_ne_zero ι).2 a0
    have h1 : ¬ P.valuation K a⁻¹ ≤ 1 := by
      rw [← hI, map_inv₀, map_inv₀]
      intro h
      have := mul_le_mul_right h (valuation k (ι a))
      rw [mul_inv_cancel₀ ha0, mul_one] at this
      exact not_le.2 ha this
    have hPa : P.valuation K a < 1 :=
      lt_of_le_of_ne ((hI a).1 ha.le) (fun h => h1 (by rw [map_inv₀, h, inv_one]))
    have hle := lt_one_le_exp hPa
    have hdiv : P.valuation K (a / N) ≤ 1 := by
      calc P.valuation K (a / N) = P.valuation K a * (P.valuation K N)⁻¹ := by rw [map_div₀, div_eq_mul_inv]
        _ ≤ P.valuation K N * (P.valuation K N)⁻¹ := mul_le_mul_left (hle.trans_eq hvN.symm) _
        _ = 1 := mul_inv_cancel₀ hvN1
    have h2 := (hI _).2 hdiv
    calc valuation k (ι a) = valuation k (ι (a / N)) * valuation k (ι N) := by
          rw [← map_mul, ← map_mul, div_mul_cancel₀ _ hN0]
      _ ≤ 1 * valuation k (ι N) := mul_le_mul_left h2 _
      _ = valuation k (ι N) := one_mul _
  have hexp : WithZero.exp (-1 : ℤ) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have K2 : valuation k (ι N) < 1 := by
    refine lt_of_le_of_ne ((hI N).2 (hvN.trans_le hexp)) fun h => ?_
    have h3 : valuation k (ι N⁻¹) ≤ 1 := by rw [map_inv₀, map_inv₀, h, inv_one]
    rw [hI, map_inv₀, hvN, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h3
    norm_num at h3
  refine ⟨Units.mk0 (ι N) ((map_ne_zero ι).2 hN0), fun x => ⟨fun hx => ?_, fun hx => lt_of_le_of_lt hx K2⟩, rfl⟩
  rw [Units.val_mk0]
  by_cases x0 : x = 0
  · rw [x0, map_zero]; exact zero_le'
  have hx0 : valuation k x ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact x0
  have hs : {y : k | valuation k (y - x) < valuation k x} ∈ 𝓝 x :=
    IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hx0, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, a, rfl⟩ := mem_closure_iff_nhds.1 (hd x) _ hs
  have e : valuation k (ι a) = valuation k x := Valuation.map_eq_of_sub_lt _ hy
  rw [← e] at hx ⊢
  exact K1 a hx

end Unif

theorem cond_unif : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (PP : Pl D.host.E), PP ∈ (pk W).Pg ∨ QAll W PP → ∀ l : LocX a (pk W).βX PP, (∃ ψk : AddChar l.k Circle, (ofSplit l.q).IsChar (pk W).ψ ψk ∧ HasConductor ψk 1) ∧ (∃ ν : Measure l.k, IsUnitVol ν) ∧ (QAll W PP → ∃ ϖ : l.kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (l.q.pr.comp (incA D)) ϖ) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a PP hPP l
  have hstd : IsStdChar D (pk W).ψ (-1) := W.Q.stdChar
  refine ⟨?_, GlobalTheory.SplitWeil.exists_isUnitVol l.k, fun hQ => ?_⟩
  · obtain ⟨⟨ψk, hψk⟩, -, hxi, -⟩ := GlobalTheory.LocChar.weil_char_split D l.k (ofSplit l.q) (pk W).ψ hstd
    exact ⟨ψk, hψk, hasConductor_weil l.q l.unit _ hstd ψk hψk hxi⟩
  · obtain ⟨t, ht⟩ := hQ
    obtain ⟨⟨p, -, hcard, hp2, -⟩, -⟩ := W.Q.charW.base.lev.Q_pl t PP ht
    have hqp : Formalism.L2.Col.qOf PP = p := by
      rw [← hcard]
      unfold Formalism.L2.Col.qOf
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hq2 : ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 := by rw [hqp]; exact hp2
    obtain ⟨k', _, _, _, _, q', hqe, -, hint', hd'⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP l.q.e l.idem
    have hint : ∀ x, (l.q.pr.comp (incA D)) x ∈ 𝒪[l.k] ↔ Formalism.L2.Col.IntAt PP x := fun x =>
      (int_transfer l.q q' hqe.symm (incA D x)).trans (hint' x)
    have hd := dense_transfer l.q q' hqe.symm hd'
    obtain ⟨ϖ, hu, hϖ⟩ := isUnif_of PP _ hint hd hq2
    exact ⟨ϖ, hu, ⟨hint, hd, rfl, hϖ⟩⟩

end GlobalTheory.WeilCondUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCharacterConductorOneExistsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_conductor_one_exists : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (PP : Pl D.host.E), PP ∈ (pk W).Pg ∨ QAll W PP → ∀ l : LocX a (pk W).βX PP, (∃ ψk : AddChar l.k Circle, (ofSplit l.q).IsChar (pk W).ψ ψk ∧ HasConductor ψk 1) ∧ (∃ ν : Measure l.k, IsUnitVol ν) ∧ (QAll W PP → ∃ ϖ : l.kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (l.q.pr.comp (incA D)) ϖ) := by
  first | exact @GlobalTheory.WeilCondUnif.cond_unif | exact GlobalTheory.WeilCondUnif.cond_unif | (intros; apply GlobalTheory.WeilCondUnif.cond_unif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAdjYZeroMulVec
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Matrix ValuativeRel IsLocalRing
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.IwaPlace NumberField Filter
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.GoodPos

variable {D : D7}

theorem incAdj_yZero_mulVec {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (z : Fin V₀.rank → D.host.E) (a : AE D) (y : Fin V₀.rank → AE D) :
    (show Matrix (Fin W.rank) (Fin V₀.rank) (AE D) from d.incAdj V₀ (a • yZero V₀ ρ z)) *ᵥ y =
      colMul d.jY r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
  have h1 : (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀)) *ᵥ y =
      Pi.single r (incA D D.host.xi0⁻¹ * hermAt V₀ y (a • ratV z)) := by
    rw [smul_mulVec, ← mulVec_mulVec, herm_eq]
    generalize gA V₀ *ᵥ y = t
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, adj, yZero, zEll, ell, Matrix.transpose_apply,
      Matrix.map_apply, Matrix.smul_apply, Matrix.neg_apply, vecMulVec_apply, RingHom.map_neg]
    by_cases hi : i = r
    · subst hi
      simp only [hr, if_true, mul_one, Pi.single_eq_same, mul_neg, RingHom.map_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
    · have : ¬ (i.1 + 1 = ρ) := fun h => hi (Fin.ext (by omega))
      simp only [this, if_false, mul_zero, neg_zero, RingHom.map_zero, zero_mul, Finset.sum_const_zero, Pi.single_eq_of_ne hi]
  change (d.jY ⬝ (incA D (-D.host.xi0⁻¹) • (adj (a • yZero V₀ ρ z) ⬝ gA V₀))) *ᵥ y = _
  rw [← mulVec_mulVec, h1, mulVec_single]
  funext k
  exact mul_comm _ _

theorem mxAt_mul {P : Pl D → Prop} {l m n : ℕ} (M : Mx D l m) {N : Mx D m n} (h : MxAt P N) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (h k j)

theorem mxAt_mul' {P : Pl D → Prop} {l m n : ℕ} {M : Mx D l m} (N : Mx D m n) (h : MxAt P M) : MxAt P (M ⬝ N) := fun i j => by
  rw [Matrix.mul_apply]; exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (h i k)

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (a : AE D) {N : Mx D m n} (h : MxAt P N) : MxAt P (a • N) := fun i j =>
  Ideal.mul_mem_left _ _ (h i j)

theorem mxAt_adj {x : Pl D} {m n : ℕ} {N : Mx D m n} (h : MxAt (· = x) N) : MxAt (· = x) (adj N) := fun i j =>
  id_conj (h j i)

def xiU (D : D7) : (AE D)ˣ := inU D.host.xi0 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem cA_xi : cA D (incA D D.host.xi0) = -incA D D.host.xi0 := by
  rw [FrameLat.cA_incA, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, RingHom.map_neg]

theorem cA_xi_inv : cA D (incA D D.host.xi0⁻¹) = -incA D D.host.xi0⁻¹ := by
  rw [FrameLat.cA_incA, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, inv_neg, RingHom.map_neg]

theorem last_of {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} {LW : Lat W}
    (hM : IsSelfDualC V₀ M) (hLW : IsSelfDualC W LW) {x : Pl D} {α m : (AE D)ˣ} {b : Fin ρ → (AE D)ˣ}
    (hb : ∀ r : Fin ρ, r.1 + 1 = ρ → b r = xiU D * cU α * m)
    (hα : ∀ y, y ∈ latA W LW (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV W LW (· = x))
    (hW : ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV W LW (· = x) ↔ cA D (b i : AE D) * a ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hρ : 0 < ρ) : ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := LocSD.isSDAt_latV D V₀ M x hM
  have hr : (⟨ρ - 1, by omega⟩ : Fin ρ).1 + 1 = ρ := by simp only; omega
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [LatMem.mem_latO_iff D V₀ W M LW hM hLW, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hα, smul_colMul, hW _ _
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (LocSD.hermAt_mem_idAt (hsd.1 y hy) _))), hb _ hr, ← int_neg,
    ← herm_conj V₀ y, int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1, Units.val_mul, Units.val_mul, RingHom.map_mul, RingHom.map_mul, cU_val, Formalism.L2.Theta.cA_cA, xiU, inU_val, cA_xi]
  have e2 := α.mul_inv
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (incA D D.host.xi0 * incA D D.host.xi0⁻¹ * cA D m * hermAt V₀ y (a • ratV z)) * e2 +
    (cA D m * hermAt V₀ y (a • ratV z)) * e3

theorem herm_kap {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (w : WO S L'') (l : Fin L.rank → AE D)
    (s : Fin S.rank → AE D) :
    hermAt S ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ l) s =
      incA D (-D.host.xi0⁻¹) * hermAt L l ((rat τ : Mx D _ _) *ᵥ ((show Matrix (Fin L''.rank) (Fin S.rank) (AE D) from w) *ᵥ s)) := by
  rw [mulVec_mulVec]
  change hermAt S ((incA D (-D.host.xi0⁻¹) • (giA S ⬝ (adj (rat τ ⬝ w) ⬝ gA L))) *ᵥ l) s = _
  generalize ((rat τ : Mx D _ _) ⬝ w : Mx D L.rank S.rank) = u
  rw [herm_eq, herm_eq, mulVec_mulVec, Matrix.mul_smul, gA_giA_cancel, smul_mulVec, dotProduct_smul, smul_eq_mul,
    ← mulVec_mulVec, dotProduct_mulVec]
  congr 2
  ext i
  simp [Matrix.vecMul, Matrix.mulVec, dotProduct, adj, map_sum, map_mul, mul_comm]

theorem kap_of {L L'' S : HSp D} (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {ζ : Fin L.rank → D.host.E}
    {ζ₀ : Fin L''.rank → D.host.E} (hζ : IsLineVec L ζ) (hζ₀ : IsLineVec L'' ζ₀) {lam : D.host.E} (hlam : lam ≠ 0)
    (hτ : τ *ᵥ ζ₀ = lam • ζ) {LL : Lat L} {LZ : Lat L''} {LS : Lat S} (hLL : IsSelfDualC L LL) (hLZ : IsSelfDualC L'' LZ)
    (hLS : IsSelfDualC S LS) {x : Pl D} {α μ : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = x) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = x))
    (hμ : ∀ a ∈ idAt D (· = x), a • ratV ζ₀ ∈ latV L'' LZ (· = x) ↔ ((μ⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x))
    (hm : ∀ a ∈ idAt D (· = x), a • ratV ζ ∈ latV L LL (· = x) ↔
      (((α * μ * inU lam hlam * (xiU D * cU α)⁻¹)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ w ∈ latO S L'' (LS : Set _) (LZ : Set _) (· = x), kap τ S w ∈ latO L S (LL : Set _) (LS : Set _) (· = x) := by
  intro w hw
  rw [LatMem.mem_latO_iff D S L'' LS LZ hLS hLZ] at hw
  have hsd := LocSD.isSDAt_latV D S LS x hLS
  have hmx : MxAt (· = x) (kap τ S w) := mxAt_smul _ (mxAt_mul _ (mxAt_mul' _ (mxAt_adj (mxAt_mul _ hw.1))))
  rw [LatMem.mem_latO_iff D L S LL LS hLL hLS]
  refine ⟨hmx, fun l hl => ?_⟩
  have hn := line_norm hζ hLL hm
  obtain ⟨a, ha, rfl⟩ := line_vec hζ (latV_idAt hl)
  rw [hα]
  refine (hsd.2.2 _ ?_).2 ?_
  · exact fun i => Ideal.mul_mem_left _ _ (mulVec_mem_idAt _ (latV_idAt hl) i)
  intro s hs
  have h1 := (hα _ _ _).1 (hw.2 s hs)
  obtain ⟨a', ha', e'⟩ := line_vec hζ₀ (latV_idAt h1)
  rw [e'] at h1
  have e2 : (show Matrix (Fin L''.rank) (Fin S.rank) (AE D) from w) *ᵥ s = ((α : AE D) * a') • ratV ζ₀ := by
    rw [mul_smul, ← e', smul_smul, Units.mul_inv, one_smul]
  have e1 := herm_smul S ((α⁻¹ : (AE D)ˣ) : AE D) 1 ((show Matrix (Fin S.rank) (Fin L.rank) (AE D) from kap τ S w) *ᵥ a • ratV ζ) s
  rw [one_smul] at e1
  rw [e1, herm_kap, e2, mulVec_smul, rat_mulVec, hτ, ratV_smul, smul_smul, herm_smul, herm_rat]
  have h2 := int_mul ((hm a ha).1 hl) (int_conj.2 ((hμ a' ha').1 h1))
  rw [hn _ h2.1] at h2
  convert h2 using 1
  generalize hm' : α * μ * inU lam hlam * (xiU D * cU α)⁻¹ = m
  have f1 := m.mul_inv
  have f2 : cA D (μ : AE D) * cA D ((μ⁻¹ : (AE D)ˣ) : AE D) = 1 := (cU μ).mul_inv
  have f3 : cA D (m : AE D) = cA D α * cA D μ * cA D (incA D lam) * (-incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ)) := by
    rw [← hm', mul_inv]
    simp only [Units.val_mul, RingHom.map_mul, inU_val, cU_inv, Formalism.L2.Theta.cA_cA, xiU, inU_inv, cA_xi_inv]
  rw [f3]
  simp only [RingHom.map_mul, RingHom.map_neg, RingHom.map_one]
  generalize incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = h
  linear_combination (cA D α * cA D (incA D lam) * incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ) * h * a * cA D a') * f2 +
    (cA D α * cA D (incA D lam) * incA D D.host.xi0⁻¹ * (α⁻¹ : (AE D)ˣ) * h * a * cA D a' * (cA D μ * cA D (μ⁻¹ : (AE D)ˣ))) * f1

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}

theorem isU_xi (h : p.UnitAA) : IsU p.v (xiU D : AE D) :=
  IsU.of_pres (xiU D).mul_inv (fun a ha => (h.1 a ha).1) fun a ha => (h.1 a ha).2

theorem isU_alpha (h : p.UnitAA) {L : HSp D} {ζ : Fin L.rank → D.host.E} (hζ : IsLineVec L ζ) {α : (AE D)ˣ}
    (hα : ∀ (S : HSp D) (L : Lat S) y, y ∈ latA S L (· = p.v) ↔ ((α⁻¹ : (AE D)ˣ) : AE D) • y ∈ latV S L (· = p.v)) :
    IsU p.v (α : AE D) := by
  have hgen : ∃ e : D.host.E, e ≠ 0 ∧ ∀ a ∈ idAt D (· = p.v),
      a • ratV ζ ∈ latV L (GlobalTheory.AdelicU.frameLat L) (· = p.v) ↔
        incA D e⁻¹ * a ∈ intAt D (· = p.v) := by
    first
    | exact GlobalTheory.GoodPos.line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L) p.v
    | exact GlobalTheory.GoodPos.line_gen hζ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat L).1 p.v
  obtain ⟨e, he, hg⟩ := hgen
  refine IsU.inv (fun a ha => ?_) α.inv_mul
  have h1 := hα L (GlobalTheory.AdelicU.frameLat L) ((incA D e * a) • ratV ζ)
  have e1 : incA D e⁻¹ * incA D e = 1 := (inU e he).inv_mul
  rw [h.2, smul_smul, hg _ (Ideal.mul_mem_left _ _ ha), hg _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ha)),
    mul_left_comm (incA D e⁻¹) ((α⁻¹ : (AE D)ˣ) : AE D), ← mul_assoc (incA D e⁻¹), e1, one_mul] at h1
  exact h1

theorem val_le_one {u : AE D} (h : IsU p.v u) : valuation k (p.pr u) ≤ 1 := by
  refine (p.int_iff _).2 ?_
  rw [p.sec_pr, mul_comm]
  exact ((h _ (FrameLat.e_mem_idAt p)).1 (FrameLat.e_mem_intAt p)).2

theorem val_eq_one {u : (AE D)ˣ} (h : IsU p.v (u : AE D)) : valuation k (p.pr u) = 1 := by
  have h1 := val_le_one h
  have h2 := val_le_one (h.inv u.mul_inv)
  have h3 : valuation k (p.pr u) * valuation k (p.pr (u⁻¹ : (AE D)ˣ)) = 1 := by
    rw [← map_mul, ← map_mul, u.mul_inv, map_one, map_one]
  exact le_antisymm h1 (by rw [← h3]; exact mul_le_of_le_one_right' h2)

end Split

end GlobalTheory.GoodPos

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPlace

theorem under_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (h : Formalism.L2.NTheta.IsIdemAt q.e PP) :
    HeightOneSpectrum.under (𝓞 D.host.F) PP = q.v := by
  have hΦ := GlobalTheory.StdFrames.comp_toAd D
  have hd := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h
  obtain ⟨ε, hε, h3⟩ := q.above
  have h2 := q.split.2.1
  have h4 := GlobalTheory.IdemSupport.ev_mul (Φ := (GlobalTheory.StdFrames.toAd D).comp (toEAf D)) q.e (cA D q.e) PP
  rw [h2, GlobalTheory.IdemSupport.ev_zero, hd.2.1, one_mul, eq_comm] at h4
  by_contra hv
  have := (GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 PP hv
  rw [← h3, GlobalTheory.IdemSupport.ev_add, h4, hd.2.1, add_zero] at this
  exact one_ne_zero this

theorem v_eq_of_isIdemAt : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (PP : Formalism.L2.DIV.Pl D.host.E),
    Formalism.L2.NTheta.IsIdemAt q.e PP → Formalism.L2.NTheta.IsIdemAt q'.e PP → q.v = q'.v :=
  fun _ _ _ _ _ _ _ _ _ _ _ q q' PP h h' => (under_eq q PP h).symm.trans (under_eq q' PP h')

end GlobalTheory.FinPl.SplitPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_baseEq_of_same_idempotentPrime : ∀ (D : D7) (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → Formalism.L2.NTheta.IsIdemAt q'.e PP → q.v = q'.v := by
  first | exact @GlobalTheory.FinPl.SplitPlace.v_eq_of_isIdemAt | exact GlobalTheory.FinPl.SplitPlace.v_eq_of_isIdemAt | (intros; apply GlobalTheory.FinPl.SplitPlace.v_eq_of_isIdemAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OverAllExists
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ValDbl

variable {D : D7}

theorem vac_at {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {v : Pl D}
    {f : WO S T → ℂ} (hv : P v) (h : Vac ψ S T LS LT P f) : Vac ψ S T LS LT (· = v) f := by
  have hle : latO S T (LS : Set _) (LT : Set _) (· = v) ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hz, rest⟩
    exact ⟨α, hα, fun v' hv' => hz v' (fun e => hv' (by subst e; exact hv)), rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sOp_smul {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (P : Pair k n)
    (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (c : ℂ) (φ₀ : GA D S → ℂ) :
    sOp β P q χ ε (c • φ₀) = c • sOp β P q χ ε φ₀ := by
  have h : formAt β P (c • φ₀) = c • formAt β P φ₀ := by
    funext P₁
    simp only [formAt, map_smul, Pi.smul_apply]
  simp only [sOp, h, map_smul, Pi.smul_apply]

theorem over_keep {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {p : SplitPt D k}
    {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m'] (hstd : IsStdChar D ψ (-1))
    {α : Frame p S m'} {β : Frame p T m} {g f : WO S T → ℂ} {Φ : Matrix m m' k → ℂ}
    (h : Over ψ α β LS LT g Φ f) :
    IsThetaFunO ψ S T f ∧ ∀ v, v ≠ p.v → Vac ψ S T LS LT (· = v) g → Vac ψ S T LS LT (· = v) f := by
  have H := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p m m' ψ hstd S T α β LS LT h.1 h.2.1 g h.2.2.1).2.1 Φ f h
  exact ⟨H.1, fun v hv hg => H.2 LS LT (· = v) (fun e => hv e.symm) hg⟩

variable {ι : Type} {p : ι → SplitPt D k} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {n n' : Type} [Fintype n]
  [DecidableEq n] [Fintype n'] [DecidableEq n'] {α : ∀ i, Frame (p i) S n'} {β : ∀ i, Frame (p i) T n} {LS : Lat S}
  {LT : Lat T} {Ψ : ι → Matrix n n' k → ℂ}

theorem overAll_nil {f f' : WO S T → ℂ} : OverAll ψ α β LS LT Ψ [] f f' ↔ f' = f := Iff.rfl

theorem overAll_cons {i : ι} {l : List ι} {f f' : WO S T → ℂ} :
    OverAll ψ α β LS LT Ψ (i :: l) f f' ↔ ∃ g, OverAll ψ α β LS LT Ψ l f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' :=
  Iff.rfl

theorem overAll_theta (hstd : IsStdChar D ψ (-1)) (l : List ι) :
    ∀ f f', OverAll ψ α β LS LT Ψ l f f' → IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' := by
  induction l with
  | nil => intro f f' h hf; rw [overAll_nil.1 h]; exact hf
  | cons i l _ =>
    intro f f' h _
    obtain ⟨g, -, hf'⟩ := overAll_cons.1 h
    exact (over_keep hstd hf').1

theorem overAll_vac (hstd : IsStdChar D ψ (-1)) (hinj : Function.Injective fun i => (p i).v) (l : List ι) :
    ∀ f f', OverAll ψ α β LS LT Ψ l f f' → ∀ j, j ∉ l →
      Vac ψ S T LS LT (· = (p j).v) f → Vac ψ S T LS LT (· = (p j).v) f' := by
  induction l with
  | nil => intro f f' h j _ hf; rw [overAll_nil.1 h]; exact hf
  | cons i l ih =>
    intro f f' h j hj hf
    obtain ⟨g, hg, hf'⟩ := overAll_cons.1 h
    have hji : j ≠ i := fun e => hj (by simp [e])
    have hjl : j ∉ l := fun h' => hj (by simp [h'])
    exact (over_keep hstd hf').2 _ (fun e => hji (hinj e)) (ih f g hg j hjl hf)

theorem overAll_last (hstd : IsStdChar D ψ (-1)) (hunit : ∀ i, (p i).UnitAA) (hinj : Function.Injective fun i => (p i).v)
    (l : List ι) : l.Nodup → ∀ f f', (∀ j, Vac ψ S T LS LT (· = (p j).v) f) → OverAll ψ α β LS LT Ψ l f f' →
      ∀ i ∈ l, ∃ g, Over ψ (α i) (β i) LS LT g (Ψ i) f' ∧ ∀ j, (j = i ∨ j ∉ l) → Vac ψ S T LS LT (· = (p j).v) g := by
  induction l with
  | nil => intro _ _ _ _ _ i hi; simp at hi
  | cons j l ih =>
    intro hl f f' hf h i hi
    rw [List.nodup_cons] at hl
    obtain ⟨g₀, hg₀, hf'⟩ := overAll_cons.1 h
    by_cases hij : i = j
    · subst hij
      refine ⟨g₀, hf', fun j' hj' => ?_⟩
      have hj'l : j' ∉ l := by
        rcases hj' with rfl | hj'
        · exact hl.1
        · exact fun h' => hj' (List.mem_cons_of_mem _ h')
      exact overAll_vac hstd hinj l f g₀ hg₀ j' hj'l (hf j')
    · have hil : i ∈ l := by simpa [hij] using hi
      obtain ⟨g₁, hg₁, hv₁⟩ := ih hl.2 f g₀ hf hg₀ i hil
      have hjv : Vac ψ S T LS LT (· = (p j).v) g₁ := hv₁ j (Or.inr hl.1)
      obtain ⟨g', hg'1, hg'2⟩ := GlobalTheory.T.splitPlaceData_distinct_places_commute D k (p i) (p j) n n' n n' ψ hstd (hunit i) (hunit j)
        (fun e => hij (hinj e)) S T (α i) (β i) (α j) (β j) LS LT g₁ g₀ f' (Ψ i) (Ψ j) hjv hg₁ hf'
      refine ⟨g', hg'2, fun j' hj' => ?_⟩
      have hne : j' ≠ j := by
        rcases hj' with rfl | hj'
        · exact hij
        · exact fun e => hj' (by simp [e])
      have hj'' : j' = i ∨ j' ∉ l := by
        rcases hj' with rfl | hj'
        · exact Or.inl rfl
        · exact Or.inr fun h' => hj' (List.mem_cons_of_mem _ h')
      exact (over_keep hstd hg'1).2 _ (fun e => hne (hinj e)) (hv₁ j' hj'')

end Local

theorem contAut_hand0 {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) {φ : GA D B.A → ℂ}
    {Ξ₁ : WO B.V₀ J.W₀ → ℂ} {Ξ₂ : WO J.W₀ B'.V₀ → ℂ} (hφ : IsContAut B.A φ) (h₁ : IsThetaFunO ψ B.V₀ J.W₀ Ξ₁)
    (h₂ : IsThetaFunO ψ J.W₀ B'.V₀ Ξ₂) : IsContAut B'.A (hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂) :=
  GlobalTheory.T.fourierJacobiHandOff_automorphic D ψ σ J B' s₂ vL _ Ξ₂ (GlobalTheory.T.bessel_level_step_fourierJacobi_period_link D ψ (σ + 1) B J s₁ B'.L B'.ζ B'.line l φ Ξ₁ hφ h₁).1 h₂

end GlobalTheory.FinPl.ValDbl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LamEqOfRed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZero

theorem lam_eq_of_red : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → ∀ (x : G.S.P.J) (g : GL (Fin D.R.r) (kP PP)), GlobalTheory.LevZero.Red G PP x g → ∀ z : 𝓞 D.host.E, Ideal.Quotient.mk PP.asIdeal z = edgeSum (GlobalTheory.chainEdge D.R.k) g → ((G.S.P.lam x : ℂˣ) : ℂ) = (G.S.ψ (((G.S.ϖ⁻¹ : G.kˣ) : G.k) * (ofSplit G.q).pr (z : D.host.E)) : ℂ) := by
  intro D c v G PP _ x g hx z hz
  have hadd : ∀ a b : D.host.E, (ofSplit G.q).pr (a + b) = (ofSplit G.q).pr a + (ofSplit G.q).pr b := by
    intro a b
    simp only [GlobalTheory.LocMod.Place.pr, map_add (f := _)]
  have hr : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  exact GlobalTheory.ChainChar.char_of_red PP.asIdeal
    (AddMonoidHom.mk' (fun y : 𝓞 D.host.E => (ofSplit G.q).pr (y : D.host.E))
      fun a b => by rw [← hadd]; rfl) hr G.S x g hx z hz

end GlobalTheory.LevZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeMoves
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeMoves
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedLat

theorem movedLat : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → ∀ g : GA D (Yc D j), ∃ M : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) M ∧ ∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P := by
  intro D L hT Gi Gl Kc Yd cX ex W _ j hj g
  obtain ⟨c, hc⟩ := W.Q.charW.base.lev.βY j hj
  have hsd : IsSelfDualC (Yc D j) ((pk W).ΛY j) := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩
  exact (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D (Yc D j) _ hsd).1 g

end GlobalTheory.MovedLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeMovesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_self_dual_lattice_moves : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → ∀ g : GA D (Yc D j), ∃ M : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) M ∧ ∀ P, GlobalTheory.FinPl.Moves (Yc D j) g ((pk W).ΛY j) M P := by
  first | exact @GlobalTheory.MovedLat.movedLat | exact GlobalTheory.MovedLat.movedLat | (intros; apply GlobalTheory.MovedLat.movedLat <;> assumption)
end
end
