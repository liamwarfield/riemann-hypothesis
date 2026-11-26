module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothOfRegularity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PosCoreQ

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section BS

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def BSR (R : ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) : Prop := ∀ g ∈ GV k r, F g ≠ 0 → gN g ≤ R

theorem smoothLev_of_ckOn {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn ⊤ (GV k r) F) (D : Set (Mx k r)) :
    SmoothLev k r 0 D F := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hF g₀ hg₀.1.1
  exact ⟨U, f', hU, hgU, hf', fun g hg hgl => hff g hg hgl.1⟩

theorem mem_level_zero_of_mem_group {g : Mat k r} (hg : g ∈ GV k r) : g ∈ Glev k r 0 :=
  ⟨hg, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

theorem tL_zero_fn (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) {g : Mat k r} (hg : g ∈ GV k r) :
    tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g = 0 := by
  have h0 : SmoothLev k r 0 Set.univ (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) :=
    fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have := (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' 0 Set.univ Y a b _ _ 1 isOpen_univ h0 h0 g
    ⟨mem_level_zero_of_mem_group hg, trivial⟩).1
  simp only [one_smul, add_zero] at this
  have h2 : tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g +
      tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g =
      tL k r z z' 0 Y a b (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) g := this.symm
  simpa using h2

theorem bsr_tL (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn ⊤ (GV k r) F) {R : ℝ} (hR : BSR R F) : BSR R (tL k r z z' 0 Y a b F) := by
  intro g hg hne
  by_contra hgt
  push Not at hgt
  let D : Set (Mx k r) := {h | R < gN h}
  have hD : IsOpen D := isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous
  have h0 : SmoothLev k r 0 D (fun _ : Mx k r => (0 : Wq →L[ℂ] Wp)) :=
    fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hloc := (Formalism.FourierDecayAlt.P.transfer_linear_local (Wq →L[ℂ] Wp) k r z z' 0 D Y a b F _ 1 hD
    (smoothLev_of_ckOn hF D) h0 g ⟨mem_level_zero_of_mem_group hg, hgt⟩).2 (fun x hx => by
      by_contra hx0
      have := hR x hx.1.1 hx0
      exact absurd hx.2 (not_lt.2 this))
  exact hne (hloc.trans (tL_zero_fn z z' Y a b hg))

end BS

section Wcell

variable {k r : ℕ}

theorem prod_w1_mem_unitary_Hpk (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (l : List (Fin r)) :
    (l.map fun a => w1 k r a (c a)).prod ∈ UH (Hpk k r) := by
  induction l with
  | nil =>
    show Matrix.conjTranspose (1 : Mx k r) * Hpk k r * 1 = Hpk k r
    simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    exact Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (Formalism.FourierDecayAlt.P.Qx3.weyl_cell_mem_unitary a (hc a)) ih

theorem wCell_mul_GV {i : Fin (r + 1)} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r)) : wCell k r i c * g ∈ GV k r :=
  Formalism.FourierDecayAlt.P.TwoByOneBlock.UH_mul (prod_w1_mem_unitary_Hpk c hc _) hg.1

end Wcell

section Pics

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem pic_of_cptClause (D : RealPlaceData k r Wp Wq) {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (K0 : Submodule ℂ (RadSp k r D.z D.z' π π'))
    (hJc : ∀ (F : Mx k r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε → (∀ (A' : ℝ) (m' : ℕ), InCC A' m' F) →
      HasCompactSupport F → (∀ g ∈ GV k r, F g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
      ∃ Φ ∈ K0, ∀ x ∈ DomR k r D.z D.z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (JF D F) x.1 x.2)
    {F : Mat k r → (Wq →L[ℂ] Wp)} {ε : ℝ} (hε : 0 < ε) (hF : JC.NiceCoef D ε F) {R : ℝ} (hR : BSR R F) :
    ∃ Φ ∈ K0, ∀ x ∈ DomR k r D.z D.z', (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = resG k r (Fin.last r) (JF D F) x.1 x.2 := by
  classical
  let Ft : Mat k r → (Wq →L[ℂ] Wp) := Set.indicator (GV k r) F
  have hE : ∀ g ∈ GV k r, F g = Ft g := fun g hg => (Set.indicator_of_mem hg F).symm
  have hFt : JC.NiceCoef D ε Ft := Formalism.FourierDecayAlt.P.JCx2.mn_nice_congr hE hF
  have hcs : HasCompactSupport Ft := by
    refine HasCompactSupport.intro (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R) fun g hg => ?_
    by_cases hgG : g ∈ GV k r
    · show Set.indicator (GV k r) F g = 0
      rw [Set.indicator_of_mem hgG]
      by_contra h0
      exact hg (hR g hgG h0)
    · exact Set.indicator_of_notMem hgG F
  obtain ⟨Φ, hΦ, hpic⟩ := hJc Ft ε hε hFt.2.1 hcs hFt.2.2
  refine ⟨Φ, hΦ, fun x hx => (hpic x hx).trans ?_⟩
  unfold resG
  have hmem := wCell_mul_GV (k := k) (i := Fin.last r) (fun a => hx.1 a) hx.2.1
  rw [Formalism.FourierDecayAlt.P.Qx8.JF_congr D (F := F) (F' := Ft) (a := 1) (fun g hg => by rw [hE g hg, one_smul]) hmem, one_smul]

end Pics

section Closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem bsr_sum {k r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Mat k r → (Wq →L[ℂ] Wp)) {R : ℝ}
    (h : ∀ i ∈ s, BSR R (f i)) : BSR R (fun g => ∑ i ∈ s, f i g) := by
  intro g hg hne
  obtain ⟨i, hi, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact h i hi g hg hne'

theorem actOp_nice_bsr (P0 : M.Par) (T : D.LevTower P0.k P0.r Wp Wq) (s : ℂ) (j : Fin (P0.r + 1))
    (w : List C.Letter) (F : Ix (Fin w.length) → Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) {ε R : ℝ}
    (hF : ∀ a, JC.NiceCoef (T.bs j) ε (F a)) (hR : ∀ a, BSR R (F a)) (a : Ix (Fin w.length)) :
    JC.NiceCoef (T.bs j) ε (D.actOp (D.RRlev T s j w) F a) ∧ BSR R (D.actOp (D.RRlev T s j w) F a) := by
  let S : D.Op (Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) → Prop := fun Θ => ∀ G, JC.NiceCoef (T.bs j) ε G → BSR R G →
    JC.NiceCoef (T.bs j) ε (D.ap Θ G) ∧ BSR R (D.ap Θ G)
  have hcl : Formalism.FourierDecayAlt.P.JCx2.mnClosed S :=
    { zero := fun G _ _ => ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero, fun g _ h => absurd rfl h⟩
      one := fun G hG hR => ⟨hG, hR⟩
      add := fun a b ha hb G hG hR => by
        obtain ⟨h1, h2⟩ := ha G hG hR
        obtain ⟨h3, h4⟩ := hb G hG hR
        refine ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_add h1 h3, fun g hg hne => ?_⟩
        by_cases h : D.ap a G g = 0
        · have : D.ap b G g ≠ 0 := by
            intro h'; apply hne; show D.ap a G g + D.ap b G g = 0; rw [h, h', add_zero]
          exact h4 g hg this
        · exact h2 g hg h
      mul := fun a b ha hb G hG hR => by
        obtain ⟨h1, h2⟩ := hb G hG hR
        exact ha _ h1 h2
      cop := fun c G hG hR => ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul c hG, fun g hg hne => hR g hg (by
        intro h0; apply hne; show c • G g = 0; rw [h0, smul_zero])⟩ }
  have hQQ : ∀ Y p q, S (D.QQlev T s j Y p q) := fun Y p q G hG hRG => by
    refine ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_smul s (Formalism.FourierDecayAlt.P.JCx2.mn_tL_nice (T.bs j) ε G Y p q hG), fun g hg hne => ?_⟩
    refine bsr_tL (T.bs j).z (T.bs j).z' Y p q hG.1 hRG g hg ?_
    intro h0; apply hne; show s • tL P0.k (P0.r - j) (T.bs j).z (T.bs j).z' 0 Y p q G g = 0; rw [h0, smul_zero]
  have hR' := Formalism.FourierDecayAlt.P.JCx2.mn_rrop_closure hcl (D.QQlev T s j) hQQ (D.positionted w)
  refine ⟨Formalism.FourierDecayAlt.P.JCx2.mn_nice_sum' _ _ fun b _ => (hR' a b (F b) (hF b) (hR b)).1, ?_⟩
  intro g hg hne
  have e : D.actOp (D.RRlev T s j w) F a g = ∑ b, D.ap (D.RRlev T s j w a b) (F b) g := by
    simp only [D.actOp, Finset.sum_apply]
  exact bsr_sum Finset.univ (fun b => D.ap (D.RRlev T s j w a b) (F b))
    (fun b _ => (hR' a b (F b) (hF b) (hR b)).2) g hg (fun h0 => hne (e.trans h0))

theorem cpt_nice_bsr {k r : ℕ} {Bs : RealPlaceData k r Wp Wq} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) :
    (∃ ε, 0 < ε ∧ JC.NiceCoef Bs ε F) ∧ ∃ R, BSR R F :=
  ⟨Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF, hF.2.1⟩

end Closure

end

end Formalism.FourierDecayAlt.P.PBF
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TopFirstOfParts
open MeasureTheory Matrix Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def DegTopOfParts : Prop := TL.WordStep → RadAATop → PolyTop → KB.DensC → KB.DegTop

section lin

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_congr_pos (Bs : B.RealPlaceData k r Wp Wq) {F F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h : ∀ g ∈ C6.domL Bs ∅, F g = F₂ g) {g : B.Mat k r} (hg : g ∈ C6.domL Bs ∅) : B.JF Bs F g = B.JF Bs F₂ g := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p F g ∂Bs.μSS = ∫ p, JF.xiP Bs p • B.rho Bs p F₂ g ∂Bs.μSS
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  have hs : B.sgs p g ∈ C6.domL Bs ∅ :=
    ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hg.1, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hg.2.1, by simp⟩
  simp only [B.rho]
  rw [h _ hs]

theorem cpt_zero' (Bs : B.RealPlaceData k r Wp Wq) : KB.CptCoef Bs (fun _ => (0 : Wq →L[ℂ] Wp)) :=
  ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero, ⟨0, fun _ _ h => (h rfl).elim⟩, ⟨1, one_pos, fun _ _ h => (h rfl).elim⟩⟩

theorem cpt_add_smul' (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (c : ℂ)
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (fun g => F₁ g + c • F₂ g) := by
  obtain ⟨s₁, ⟨R₁, hR₁⟩, ⟨ε₁, hε₁, hG₁⟩⟩ := h₁
  obtain ⟨s₂, ⟨R₂, hR₂⟩, ⟨ε₂, hε₂, hG₂⟩⟩ := h₂
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add s₁ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul c s₂), ⟨max R₁ R₂, fun g hg hne => ?_⟩,
    ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun g hg hne => ?_⟩⟩
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (hR₂ g hg this).trans (le_max_right _ _)
    · exact (hR₁ g hg h0).trans (le_max_left _ _)
  · by_cases h0 : F₁ g = 0
    · have : F₂ g ≠ 0 := fun h2 => hne (by simp [h0, h2])
      exact (min_le_right _ _).trans (hG₂ g hg this)
    · exact (min_le_left _ _).trans (hG₁ g hg h0)

theorem cpt_add (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (fun g => F₁ g + F₂ g) := by
  have := cpt_add_smul' Bs (1 : ℂ) h₁ h₂
  simpa [one_smul] using this

theorem cpt_sub (Bs : B.RealPlaceData k r Wp Wq) {F₁ F₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂) : KB.CptCoef Bs (fun g => F₁ g - F₂ g) := by
  have := cpt_add_smul' Bs (-1 : ℂ) h₁ h₂
  simpa [neg_one_smul, ← sub_eq_add_neg] using this

theorem cpt_smul (Bs : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (c : ℂ)
    (h : KB.CptCoef Bs F) : KB.CptCoef Bs (fun g => c • F g) := by
  have := cpt_add_smul' Bs c (cpt_zero' Bs) h
  simpa using this

theorem gN_bound (Bs : B.RealPlaceData k r Wp Wq) {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef Bs F) (A : ℝ)
    (hA : 0 ≤ A) : ∃ c : ℝ, 0 ≤ c ∧ ∀ g ∈ B.GV k r, ‖F g‖ ≤ c * B.gN g ^ (-A) := by
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV.cpt_bound Bs F hF A hA
  refine ⟨max c 0, le_max_right _ _, fun g hg => ?_⟩
  have hg1 : 1 ≤ B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have hpos : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (by linarith) A
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc ‖F g‖ * B.gN g ^ A = B.gN g ^ A * ‖F g‖ := mul_comm _ _
    _ ≤ c := hc g hg
    _ ≤ max c 0 := le_max_left _ _

theorem vecV_sub (Bs : B.RealPlaceData k r Wp Wq) (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt)
    {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)} (h₁ : KB.CptCoef Bs H₁) (h₂ : KB.CptCoef Bs H₂) :
    D.vecV Bs ν' m₀ (fun g => H₁ g - H₂ g) q = D.vecV Bs ν' m₀ H₁ q - D.vecV Bs ν' m₀ H₂ q := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  set A : ℝ := max 0 (c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)) with hAdef
  obtain ⟨c₁, hc₁0, hb₁⟩ := gN_bound Bs h₁ A (le_max_left _ _)
  obtain ⟨c₂, hc₂0, hb₂⟩ := gN_bound Bs h₂ A (le_max_left _ _)
  have h₁₂ := cpt_sub Bs h₁ h₂
  unfold D.vecV
  by_cases h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos h]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
      obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
      have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
      have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
        ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
      have hZm := hZ.trans hmono
      obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd hZm hpos (le_max_right _ _)
      have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs h'.choose _ _ :=
        ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZm, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZm,
          fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZm hρ⟩
      have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
      have hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF → KB.CptCoef Bs G →
          (∀ g ∈ B.GV k r, ‖G g‖ ≤ cF * B.gN g ^ (-A)) →
          D.orbJ Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) G =
              ∫ p, θ p • D.orbIntegrand Bs h'.choose G p ∂Bs.μSS ∧
            Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := by
        intro G cF hcF hGc hGb
        have hm : AEStronglyMeasurable (D.orbIntegrand Bs h'.choose G) Bs.μSS :=
          Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb ((Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn hGc.1).mono fun g hg => hg.1)
        have hi : Integrable (fun p => θ p • D.orbIntegrand Bs h'.choose G p) Bs.μSS :=
          Integrable.mono' (hmaj.const_mul cF) (hθ.1.aestronglyMeasurable.smul hm)
            (hdom G cF hcF fun p hp => hGb _ (Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ))
        refine ⟨?_, hi⟩
        have hex : ∃ θ', D.IsNormCut Bs h'.choose (D.muR Bs h'.choose (h.1.2 ▸ D.ptPerm q)) θ' ∧
            Integrable (fun p => θ' p • D.orbIntegrand Bs h'.choose G p) Bs.μSS := ⟨θ, hθ, hi⟩
        unfold D.orbJ
        rw [dif_pos hex]
        exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs h'.choose _ hrel hR G _ θ hex.choose_spec.1 hθ
          hex.choose_spec.2 hi
      obtain ⟨e1, i1⟩ := hEq H₁ c₁ hc₁0 h₁ hb₁
      obtain ⟨e2, i2⟩ := hEq H₂ c₂ hc₂0 h₂ hb₂
      obtain ⟨e12, -⟩ := hEq (fun g => H₁ g - H₂ g) (c₁ + c₂) (add_nonneg hc₁0 hc₂0) h₁₂ (fun g hg =>
        (norm_sub_le _ _).trans (by rw [add_mul]; exact add_le_add (hb₁ g hg) (hb₂ g hg)))
      rw [e12, e1, e2, ← integral_sub i1 i2]
      congr 1
      funext p
      simp only [D.orbIntegrand, B.rho, ContinuousLinearMap.sub_comp,
        ContinuousLinearMap.comp_sub, smul_sub]
    · simp only [dif_neg h', sub_zero]
  · simp only [dif_neg h, sub_zero]

end lin

section rad

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem cell_dom {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {x : (Fin P.r → ℂ) × Q.Mx P.k P.r}
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') : Q.wCell P.k P.r (Fin.last P.r) x.1 * x.2 ∈ C6.domL Bs ∅ := by
  have h := (Formalism.FourierDecayAlt.P.big_cell_values P.k P.r Wp Wq Bs x hx).1
  exact ⟨h.1, h.2.1, by simp⟩

theorem isRadOf_congr {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    {F F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hΦ : Top.IsRadOf P Bs Φ F) (h : ∀ g ∈ C6.domL Bs ∅, F g = F₂ g) :
    Top.IsRadOf P Bs Φ F₂ := by
  intro x hx
  rw [hΦ x hx]
  simp only [Q.resG]
  rw [jf_congr_pos Bs h (cell_dom Bs hx)]

theorem isRadOf_sub {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) {Φ₁ Φ₂ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    {F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (h₁ : KB.CptCoef Bs F₁) (h₂ : KB.CptCoef Bs F₂)
    (hΦ₁ : Top.IsRadOf P Bs Φ₁ F₁) (hΦ₂ : Top.IsRadOf P Bs Φ₂ F₂) :
    Top.IsRadOf P Bs (Φ₁ - Φ₂) (fun g => F₁ g - F₂ g) := by
  intro x hx
  have h₂' := cpt_smul Bs (-1 : ℂ) h₂
  obtain ⟨ε₁, hε₁, hn₁⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt h₁
  obtain ⟨ε₂, hε₂, hn₂⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt h₂'
  have e : (fun g => F₁ g - F₂ g) = fun g => F₁ g + (-1 : ℂ) • F₂ g := by
    funext g; rw [neg_one_smul, sub_eq_add_neg]
  rw [e]
  simp only [Submodule.coe_sub, Pi.sub_apply]
  rw [hΦ₁ x hx, hΦ₂ x hx]
  simp only [Q.resG]
  rw [Formalism.FourierDecayAlt.P.JCx2.bc_JF_add (Formalism.FourierDecayAlt.P.TLB.nice_mono hn₁ (min_le_left ε₁ ε₂))
    (Formalism.FourierDecayAlt.P.TLB.nice_mono hn₂ (min_le_right ε₁ ε₂)) (Formalism.FourierDecayAlt.P.TLB.wCell_om Bs hx),
    Formalism.FourierDecayAlt.P.JCx2.bc_JF_smul, smul_add, neg_one_smul, smul_neg, sub_eq_add_neg]

theorem radExists {P : M.Par} (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (hF : KB.CptCoef p.T.base F) : ∃ Φ, Top.IsRadOf P p.T.base Φ F := by
  obtain ⟨ε, hε, hn⟩ := Formalism.FourierDecayAlt.P.TLB.nice_of_cpt hF
  obtain ⟨Φ, hΦ⟩ := Formalism.FourierDecayAlt.P5.radJFExists Wp Wq P p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' p.T.base F
    p.hP rfl rfl rfl rfl ⟨hn.2.1, ε, hε, hn.2.2⟩
  exact ⟨Φ, hΦ⟩

theorem vecV_eq_of_rad (hDC : KB.DensC) {P : M.Par} (p : KB.Pl P Wp Wq) {F₁ F₂ : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    (h₁ : KB.CptCoef p.T.base F₁) (h₂ : KB.CptCoef p.T.base F₂) {Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π'}
    (hΦ₁ : Top.IsRadOf P p.T.base Φ F₁) (hΦ₂ : Top.IsRadOf P p.T.base Φ F₂) (a : C.LPt) : p.V F₁ a = p.V F₂ a := by
  have h0 := isRadOf_sub p.T.base h₁ h₂ hΦ₁ hΦ₂
  rw [sub_self] at h0
  have hv := hDC Wp Wq P p _ (cpt_sub p.T.base h₁ h₂) h0 a
  have e := vecV_sub p.T.base p.ν' p.m₀ a h₁ h₂
  unfold KB.Pl.V at hv ⊢
  rw [e] at hv
  exact sub_eq_zero.1 hv

end rad

end Formalism.FourierDecayAlt.P.PBN
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.JfSmoothBuiltOfLeaves
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def GEqs (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : B.Mat k r → E) : Prop :=
  Q.CkLev k r 0 (2 * r + k + 1) (Q.OmPlus k r z z') J ∧
  (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Formalism.REAL.RdV X J g = c • J g) ∧
  (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.LdV X J g = c • J g) ∧
  (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z] Bs → ∀ w : ℂ, ∃ c : ℂ,
    ∀ g ∈ JF.Om k r z z', Q.capLft k r Bs w J g = c • J g) ∧
  (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z'] Bs → ∀ w : ℂ, ∃ c : ℂ,
    ∀ g ∈ JF.Om k r z z', Q.capR k r Bs w J g = c • J g) ∧
  (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ JF.Om k r z z', Q.CV k r (Y : ℂ) J g = c • J g)

def NDiff : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (m : ℕ∞) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    J ∈ Gr.FFlM m k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Formalism.REAL.RdV X J g = c • J g) ∧
    (∀ X ∈ JfS.lieOf (Nset k r), ∃ c : ℂ, ∀ g ∈ JF.Om k r D.z D.z', Q.LdV X J g = c • J g)

def UCap : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (u u' : ℕ → ℝ) (J : B.Mat k r → (Wq →L[ℂ] Wp)),
    Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' →
    J ∈ Gr.FFlM ((2 * r + k + 1 : ℕ) : ℕ∞) k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') →
    (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [D.z] Bs → ∀ w : ℂ, ∃ c : ℂ,
      ∀ g ∈ JF.Om k r D.z D.z', Q.capLft k r Bs w J g = c • J g) ∧
    (∀ Bs : Fin k → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [D.z'] Bs → ∀ w : ℂ, ∃ c : ℂ,
      ∀ g ∈ JF.Om k r D.z D.z', Q.capR k r Bs w J g = c • J g)

def GEqsPost : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : B.Mat k r → E) (ℓ : E →L[ℂ] ℂ), GEqs k r z z' J → GEqs k r z z' (fun g => ℓ (J g))

def SmoothOfCoeffs : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (Dm : Set (B.Mat k r))
    (J : B.Mat k r → E), (∀ ℓ : E →L[ℂ] ℂ, Q.SmoothLev k r 0 Dm (fun g => ℓ (J g))) → Q.SmoothLev k r 0 Dm J

def GChart : Prop :=
  ∀ (k r : ℕ), ∃ d : ℕ, ∀ g₀ ∈ B.GV k r, ∃ (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)),
    IsOpen O ∧ IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ κ O ∧ ContDiffOn ℝ ∞ Φ U ∧
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) ∧ (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g)

def ChartEqs : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (d : ℕ) (O : Set (Fin d → ℝ)) (U : Set (B.Mat k r))
    (κ : (Fin d → ℝ) → B.Mat k r) (Φ : B.Mat k r → (Fin d → ℝ)) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    IsOpen O → IsOpen U → ContDiffOn ℝ ∞ κ O → ContDiffOn ℝ ∞ Φ U →
    (∀ x ∈ O, κ x ∈ B.GV k r ∧ κ x ∈ U ∧ Φ (κ x) = x) → (∀ g ∈ U, g ∈ B.GV k r → Φ g ∈ O ∧ κ (Φ g) = g) →
    (∀ x ∈ O, κ x ∈ Q.OmPlus k r z z') → GEqs k r z z' u →
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → SOp d),
      (∀ j i w, ContDiffOn ℝ ∞ ((P j).a i w) O) ∧ (∀ j, (P j).ord ≤ 2 * r + k + 1) ∧
      ContDiffOn ℝ ((2 * r + k + 1 : ℕ) : WithTop ℕ∞) (fun x => u (κ x)) O ∧
      (∀ j, ∀ x ∈ O, (P j).app (fun y => u (κ y)) x = 0) ∧
      ∀ x ∈ O, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → (∀ j, (P j).symb x ξ = 0) →
        ∃ Ξ : B.Mat k r, B.inLie k r Ξ ∧ Ξ ≠ 0 ∧ IsNilpotent Ξ ∧
          (∀ X ∈ JfS.lieOf (UWset k r z) ∪ JfS.lieOf (Nset k r), (Matrix.trace (Ξ * X)).re = 0) ∧
          (∀ X ∈ JfS.lieOf (UWset k r z') ∪ JfS.lieOf (Nset k r),
            (Matrix.trace (Ξ * (κ x * X * (κ x)⁻¹))).re = 0)

def ClassToWeak : Prop :=
  ∀ (d N : ℕ) (P : SOp d) (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → ℂ),
    IsOpen U → (∀ i w, ContDiffOn ℝ ∞ (P.a i w) U) → P.ord ≤ N → ContDiffOn ℝ (N : WithTop ℕ∞) u U →
    (∀ x ∈ U, P.app u x = 0) →
    ∀ φ : (Fin d → ℝ) → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x, u x * P.tr φ x = 0

def LieSsetSplit : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ X ∈ JfS.lieOf (Sset k r z), ∃ A ∈ JfS.lieOf (UWset k r z), ∃ Bn ∈ JfS.lieOf (Nset k r), X = A + Bn

def GRegScalar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (u : B.Mat k r → ℂ),
    1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → GEqs k r z z' u →
    Q.SmoothLev k r 0 (Q.OmPlus k r z z') u

theorem gRegJ_of (hN : NDiff) (hU : UCap) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hS : GRegScalar) : GRegJ := by
  intro k r Wp Wq _ _ _ _ _ _ D u u' J hT hT' hF hCV
  have hG : GEqs k r D.z D.z' J := by
    obtain ⟨hn1, hn2⟩ := hN k r Wp Wq D _ J hF
    obtain ⟨hu1, hu2⟩ := hU k r Wp Wq D u u' J hT hT' hF
    refine ⟨?_, hn1, hn2, hu1, hu2, hCV⟩
    intro g₀ hg₀
    obtain ⟨U, F, hUo, hgU, hFc, hJF⟩ := hF.1 g₀ hg₀
    exact ⟨U, F, hUo, hgU, by simpa [Gr.smM] using hFc, hJF⟩
  exact hC k r (Wq →L[ℂ] Wp) _ J (fun ℓ =>
    hS k r D.z D.z' _ D.k_pos D.z_mem D.z'_mem D.T_pos D.T'_pos (hP k r D.z D.z' _ J ℓ hG))

theorem gRegScalar_of (hK : GChart) (hE : ChartEqs) (hW : ClassToWeak) (hR : EllRegW) (hSym : JfS.SymbolNil)
    (hL : LieSsetSplit) : GRegScalar := by
  intro k r z z' u hk hz hz' hT hT' hG g₀ hg₀
  obtain ⟨d, hd⟩ := hK k r
  have hg₀G : g₀ ∈ B.GV k r := hg₀.1.1
  obtain ⟨O, U, κ, Φ, hO, hU, hg₀U, hκ, hΦ, hκO, hΦU⟩ := hd g₀ hg₀G
  have hO' : IsOpen (O ∩ κ ⁻¹' Q.OmPlus k r z z') :=
    hκ.continuousOn.isOpen_inter_preimage hO (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open z z')
  have hU' : IsOpen (U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z')) :=
    hΦ.continuousOn.isOpen_inter_preimage hU hO'
  have hΦg₀ : Φ g₀ ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z' := by
    obtain ⟨h1, h2⟩ := hΦU g₀ hg₀U hg₀G
    refine ⟨h1, ?_⟩
    show κ (Φ g₀) ∈ Q.OmPlus k r z z'
    rw [h2]; exact hg₀.2
  have hκO' : ∀ x ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z',
      κ x ∈ B.GV k r ∧ κ x ∈ U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z') ∧ Φ (κ x) = x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hκO x hx.1
    refine ⟨h1, ⟨h2, ?_⟩, h3⟩
    show Φ (κ x) ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z'
    rw [h3]; exact hx
  have hΦU' : ∀ g ∈ U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z'), g ∈ B.GV k r →
      Φ g ∈ O ∩ κ ⁻¹' Q.OmPlus k r z z' ∧ κ (Φ g) = g :=
    fun g hg hgG => ⟨hg.2, (hΦU g hg.1 hgG).2⟩
  obtain ⟨ι, hι, P, hPc, hPo, huc, hPu, hsym⟩ := hE k r z z' d _ _ κ Φ u hk hz hz' hT hT' hO' hU'
    (hκ.mono Set.inter_subset_left) (hΦ.mono Set.inter_subset_left) hκO' hΦU' (fun x hx => hx.2) hG
  have := hι
  have hsm : ContDiffOn ℝ ∞ (fun x => u (κ x)) (O ∩ κ ⁻¹' Q.OmPlus k r z z') := by
    refine hR d ι P _ _ hO' hPc huc.continuousOn
      (fun j φ hφ hφc hφs => hW d _ (P j) _ _ hO' (hPc j) (hPo j) huc (hPu j) φ hφ hφc hφs) ?_
    intro x hx ξ hξ
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨Ξ, hΞ, hΞ0, hnil, hl, hr⟩ := hsym x hx ξ hξ hall
    apply hΞ0
    have hxG := (hκO' x hx).1
    have hxOm : κ x ∈ Q.OmPlus k r z z' := hx.2
    refine hSym k r z z' hk hz hz' hT hT' (κ x) hxG ⟨hxOm.2, fun a => hxOm.1 ⟨(a : ℕ) + 1, by omega⟩ a.isLt⟩
      Ξ hΞ hnil ?_ ?_
    · intro X hX
      obtain ⟨A, hA, Bn, hB, rfl⟩ := hL k r z hz hT X hX
      simp only [mul_add, Matrix.trace_add, Complex.add_re]
      rw [hl A (Or.inl hA), hl Bn (Or.inr hB), add_zero]
    · intro X hX
      obtain ⟨A, hA, Bn, hB, rfl⟩ := hL k r z' hz' hT' X hX
      simp only [mul_add, add_mul, Matrix.trace_add, Complex.add_re]
      rw [hr A (Or.inl hA), hr Bn (Or.inr hB), add_zero]
  refine ⟨U ∩ Φ ⁻¹' (O ∩ κ ⁻¹' Q.OmPlus k r z z'), fun g => u (κ (Φ g)), hU', ⟨hg₀U, hΦg₀⟩, ?_, ?_⟩
  · exact hsm.comp (hΦ.mono Set.inter_subset_left) (fun g hg => hg.2)
  · intro g hg hgG
    show u g = u (κ (Φ g))
    rw [(hΦU g hg.1 hgG.1).2]

theorem jfSmoothBuilt_of_leaves (hN : NDiff) (hU : UCap) (hP : GEqsPost) (hC : SmoothOfCoeffs) (hK : GChart)
    (hE : ChartEqs) (hW : ClassToWeak) (hR : EllRegW) (hSym : JfS.SymbolNil) (hL : LieSsetSplit) :
    JfSmoothBuilt :=
  transfer_smooth_of_regularity (gRegJ_of hN hU hP hC (gRegScalar_of hK hE hW hR hSym hL))

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselFunctionalOfSigmaContinuity
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularityBundleFromHypotheses
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.FourierDecayAlt.P.S3dx4

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

theorem quadConv_of (hSch : SchurH) (hNIs : NormIdSm) (hNI : NormInv) (hGS : GrowthS) (hGG : GrowthG)
    (hDD : DecDD) (hBC : BeConv) : More.QuadConv := by
  intro hIn k r Wp Wq _ _ _ _ _ _ _ _ D ε lam h H _ _ _ σ w0 u u' νq νq' hS1 hS2 l l' hbe hbe'
  exact ⟨fun γ hγ => quadA_of hSch hNIs hNI hGG hDD hBC hIn D hS1 hS2 hbe hbe' hγ,
    quadB_of hNI hGS hGG hDD hIn D hS1 hbe⟩

end Formalism.FourierDecayAlt.P.S3dx4

theorem Formalism.FourierDecayAlt.P.regularity_bundle_from_hypotheses : Formalism.FourierDecayAlt.ThreeDimData.More.MoreOfSteps :=
  fun hSch hNIs hNI hGS hGG hDD hBC _ =>
    ⟨Formalism.FourierDecayAlt.P.S3dx4.phiReg_of hSch hNIs hGG hDD hBC, Formalism.FourierDecayAlt.P.S3dx4.ooConv_of hSch hNIs hNI hGG hDD hBC,
      Formalism.FourierDecayAlt.P.S3dx4.quadConv_of hSch hNIs hNI hGS hGG hDD hBC⟩
end
end

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.ThreeDimData

theorem shape_true : Shape :=
  DDSmoothness.shape_of psi_constant schur_hermitian bessel_convergence norm_identity_smooth bessel_function_bound

theorem k_finite_form : KFinForm :=
  DDSmoothness.kFinForm_of psi_constant bessel_convergence bessel_function_bound

theorem zeroCase_true : ZeroCase :=
  UnipotentHaarMeasurability.zeroCase_of bessel_convergence norm_identity_smooth schur_hermitian

theorem zero_case_discrete_series : ZeroCaseDD :=
  UnipotentHaarMeasurability.zeroCaseDD_of bessel_convergence norm_identity_smooth schur_hermitian

theorem discrete_series_form_one : DDFormOne :=
  discrete_series_form_one_reduction psi_constant schur_hermitian norm_inverse_bound growth_spherical_bound
    growth_group_bound double_coset_decomposition bessel_convergence norm_identity_smooth bessel_function_bound shape_true

theorem admissible_atomic_form_one : AtFormAdmOne :=
  admissible_atomic_form_one_reduction schur_hermitian bessel_convergence norm_identity_smooth bessel_function_bound
    shape_true k_finite_form zeroCase_true zero_case_discrete_series

theorem orbit_convergence_discrete_series : OrbConvDD :=
  S3dx4.orbConvDD_of_decDD double_coset_decomposition

theorem bessel_nonzero_l2 : BesselNonvanishingL2 :=
  MatrixMultiplicationContinuity.bessel_nonzero_l2_reduction schur_hermitian norm_inverse_bound growth_spherical_bound growth_group_bound
    double_coset_decomposition bessel_convergence

theorem regularity_and_convergence_bundle : More.PhiReg ∧ More.OOConv ∧ More.QuadConv :=
  regularity_bundle_from_hypotheses schur_hermitian norm_identity_smooth norm_inverse_bound growth_spherical_bound growth_group_bound
    double_coset_decomposition bessel_convergence orbit_convergence_discrete_series

theorem orbit_integral_convergence : More.OOConv := regularity_and_convergence_bundle.2.1

theorem quadratic_convergence : More.QuadConv := regularity_and_convergence_bundle.2.2

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Dmin_castM {k a b : ℕ} (e : a = b) (z z' : Fin (2 * b + k + 1) → ℂ) (g : B.Mat k a) (l : ℕ)
    (hl : l < b + 2) (hl' : l < a + 2) :
    Dmin k b z z' (D.castM e g) ⟨l, hl⟩ = Dmin k a (D.castV e.symm z) (D.castV e.symm z') g ⟨l, hl'⟩ := by
  subst e
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self, Formalism.FourierDecayAlt.P.JCTx6.Link2.castV_self]

theorem sliceAt_lincomb (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef T.base F)
    (i : ℕ) (hi : i ≤ r) (hi1 : 1 ≤ i) (p : C.LPt) (hp : D.IsLocPt p i)
    {ι : Type} (S : Finset ι) (c : ι → ℂ) (ws : ι → List C.Letter) (as : ∀ q, Wd.Ix (Fin (ws q).length))
    (Hf : B.Mat k r → (Wq →L[ℂ] Wp))
    (hG : ∀ g ∈ B.GV k r, Dmin k r T.base.z T.base.z' g ⟨i, by omega⟩ ≠ 0 →
      Hf g = ∑ q ∈ S, c q • D.uwG k r T.base.z T.base.z' F i hi (ws q) (as q) g)
    (γ : B.Mat k (r - D.ptSize p)) (hγ : γ ∈ B.GV k (r - D.ptSize p)) :
    D.sliceAt k r T.base.z T.base.z' Hf p γ =
      ∑ q ∈ S, c q • D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' F i hi (ws q) (as q)) p γ := by
  revert γ

  obtain ⟨h, n, t, rfl⟩ : ∃ (h : C.LPt) (n : ℕ) (t : ℂ), p = h ++ [(n + 1, t)] := by
    have hne : p ≠ [] := by
      rintro rfl
      have := hp.2
      simp [D.ptSize] at this
      omega
    refine ⟨p.dropLast, (p.getLast hne).1 - 1, (p.getLast hne).2, ?_⟩
    have h1 : 1 ≤ (p.getLast hne).1 := (hp.1 _ (List.getLast_mem hne)).1
    rw [Nat.sub_add_cancel h1]
    exact (List.dropLast_append_getLast hne).symm
  obtain ⟨hpb, hps⟩ := hp
  subst hps
  set ph := D.ptSize h with hph
  have hP : D.ptSize (h ++ [(n + 1, t)]) = ph + (n + 1) := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h (n + 1) t
  have ht : t ≠ 0 := (hpb (n + 1, t) (by simp)).2
  have hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)])) := ⟨hpb, rfl⟩
  have hlocH := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2
  set ρ := r - D.ptSize (h ++ [(n + 1, t)]) with hρ
  intro γ hγ
  have hsum : ph + (n + 1) + ρ = r := by omega
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  have hσ : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h)) (Fin.cast hP q)).val = (D.ptPerm (h ++ [(n + 1, t)]) q).val := by
    intro q
    rw [hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨q.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t (Fin.cast hP q) = D.ptDiag (h ++ [(n + 1, t)]) q := by
    intro q
    simp only [D.ptDiag]
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]
  have hdP : ∀ q, Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t q ≠ 0 := by
    intro q
    refine Fin.addCases (fun i => ?_) (fun i => ?_) q
    · simp only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; exact hd0 i
    · simp only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]; exact ht

  have hS : ∀ Gw : B.Mat k r → (Wq →L[ℂ] Wp), D.sliceAt k r T.base.z T.base.z' Gw (h ++ [(n + 1, t)]) γ =
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) Gw) (fun a => a.elim0) γ := by
    intro Gw
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gw) γ
    unfold D.sliceAt
    rw [dite_eq_left (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  have e1 : r = ph + (n + 1) + ρ := hsum.symm
  have e2 : ph + (n + 1) + ρ = r := hsum
  have hj1 : 1 ≤ ph + (n + 1) := by omega
  obtain ⟨hFs, ⟨R, hR⟩, ⟨ε, hε, hGε⟩⟩ := hF

  have hcut : ∀ x ∈ B.GV k (ph + (n + 1) + ρ), D.castF e2 F x =
      ((Formalism.FourierDecayAlt.P.Topx2.chi0 (Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) •
        D.castF e2 F x := by
    intro x hx
    by_cases h0 : D.castF e2 F x = 0
    · rw [h0, smul_zero]
    · have hxG := Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hx
      have h1 : ε ≤ Gf k r T.base.z T.base.z' (D.castM e2 x) := hGε _ hxG h0
      rw [show Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') x =
        Gf k r T.base.z T.base.z' (D.castM e2 x) from Formalism.FourierDecayAlt.P.PBE.Gf_castM e2 _ _ x]
      rw [Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation.2.2 _ ((one_le_div hε).2 h1)]
      simp
  have hfA : ∀ (A₀ : ℝ) (m : ℕ), B.InCC A₀ m (D.castF e2 F) := fun A₀ m =>
    Formalism.FourierDecayAlt.P.JCTx6.Link2.inCC_castF e2 (Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hFs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R)
      (fun g hg hgC => by
        by_contra h0
        exact hgC (hR g hg h0)) A₀ m)

  obtain ⟨Cq, hCq0, hCq⟩ := Formalism.FourierDecayAlt.P.PBE.posCoreQ
  have hInt : ∀ (w : List C.Letter) (a : Wd.Ix (Fin w.length)), Integrable
      (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) =>
        U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
          (D.castV e1 T.base.z) (D.castV e1 T.base.z') ξ •
          D.castF e2 (D.uwG k r T.base.z T.base.z' F (D.ptSize (h ++ [(n + 1, t)])) hi w a)
            (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
              (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ))
      (U.muXi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))) := by
    intro w a
    set Gw := D.uwG k r T.base.z T.base.z' F (D.ptSize (h ++ [(n + 1, t)])) hi w a with hGw
    obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z)
      (D.castV e1 T.base.z') (by omega) w a hj1
    have hG1 : D.castF e2 Gw = D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 F) (ph + (n + 1)) (by omega) w a := by
      rw [hGw, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hP _ _ w a
    have hFrel : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
        D.castF e2 Gw g = B.opApply Θ (fun x => ((Formalism.FourierDecayAlt.P.Topx2.chi0 (Gf k (ph + (n + 1) + ρ)
          (D.castV e1 T.base.z) (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 F x) g := by
      intro g hg hD
      rw [hG1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFs) g hg hD]
      exact Formalism.FourierDecayAlt.P.PBE.opApply_congrGV Θ hcut g hg
    set o := w.length * (ph + (n + 1))
    set κ := w.length * (ph + (n + 1)) + w.length * (ph + (n + 1)) ^ 2
    set As : ℕ := o + (κ + (ph + (n + 1)) * o) + (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 with hAs
    obtain ⟨cc, hcc⟩ := hfA (Cq * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ)) (3 * As)
    obtain ⟨ε', K, -, -, hmain⟩ := hCq k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
      (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
      Θ o κ hΘ Formalism.FourierDecayAlt.P.Topx2.chi0 (Cq * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ)) ε
      Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hε (D.ptPerm h) (D.ptDiag h) t hd0 ht As 0 0
      (by omega) (by omega) (by omega) (by omega) (by positivity) le_rfl
    exact (hmain (D.castF e2 F) cc hcc (D.castF e2 Gw) hFrel).2.2 γ hγ

  have hZ0 : G.detM (fun a => a.elim0 : G.Mat 0) ≠ 0 := by
    unfold G.detM; rw [Matrix.det_isEmpty]; exact one_ne_zero
  have hdh0 : (U.hMat (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t)).det ≠ 0 :=
    Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hdP
  have hpt : ∀ ξ : U.Xi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)),
      D.castF e2 Hf (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
          (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ) =
        ∑ q ∈ S, c q • D.castF e2 (D.uwG k r T.base.z T.base.z' F (D.ptSize (h ++ [(n + 1, t)])) hi (ws q) (as q))
          (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
            (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ) := by
    intro ξ
    set g := U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
      (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ with hg
    have hgG : g ∈ B.GV k (ph + (n + 1) + 0 + ρ) :=
      Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation _ _ hdP ξ _ hZ0 hγ
    have hDj : U.DjU k (ph + (n + 1) + 0) ρ g = _ :=
      Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice _ _ ξ _ γ
    have hD : Dmin k r T.base.z T.base.z' (D.castM e2 g) ⟨D.ptSize (h ++ [(n + 1, t)]), by omega⟩ ≠ 0 := by
      rw [Dmin_castM e2 _ _ g _ _ (by omega)]
      have e3 : (⟨D.ptSize (h ++ [(n + 1, t)]), by omega⟩ : Fin (ph + (n + 1) + ρ + 2)) = ⟨ph + (n + 1), by omega⟩ :=
        Fin.ext hP
      rw [e3, Formalism.FourierDecayAlt.P.hat_z_minimum_degree k (ph + (n + 1)) ρ]
      show U.DjU k (ph + (n + 1) + 0) ρ g ≠ 0
      rw [hDj]
      exact mul_ne_zero hdh0 hZ0
    show Hf (D.castM e2 g) = ∑ q ∈ S, c q • D.uwG k r T.base.z T.base.z' F _ hi (ws q) (as q) (D.castM e2 g)
    exact hG _ (Formalism.FourierDecayAlt.P.PBE.castM_GV e2 hgG) hD
  rw [hS Hf]
  simp_rw [hS]
  unfold U.PhiFun
  have key : ∀ q ∈ S, Integrable (fun ξ : U.Xi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) =>
      c q • (U.psiStar (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
          (D.castV e1 T.base.z) (D.castV e1 T.base.z') ξ •
          D.castF e2 (D.uwG k r T.base.z T.base.z' F (D.ptSize (h ++ [(n + 1, t)])) hi (ws q) (as q))
            (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
              (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ)))
      (U.muXi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))) :=
    fun q _ => MeasureTheory.Integrable.smul (c q) (hInt (ws q) (as q))
  rw [Finset.sum_congr rfl (fun q _ => (integral_smul (c q) _).symm), ← integral_finsetSum S key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [hpt ξ, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_comm]

end Formalism.FourierDecayAlt.P.PBG
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHRepLin
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem repLin_nice {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
    (T : D.LevTower P.k P.r Wp Wq) (j : ℕ) (G : ℂ → B.Mat P.k (P.r - (j + 1)) → (Wq →L[ℂ] Wp))
    (hG : GoodFam T j G) (t : ℂ) (ht : t ≠ 0) :
    ∃ ε, 0 < ε ∧ JC.NiceCoef (T.bs (j + 1)) ε (G t) := by
  obtain ⟨hG1, hG2⟩ := hG
  obtain ⟨C, hC, ε, hε, hCε⟩ := hG2 {t} isCompact_singleton (fun s hs => by rw [Set.mem_singleton_iff.mp hs]; exact ht)
  have hsupp : ∀ γ, G t γ ≠ 0 → γ ∈ C := fun γ h => (hCε t rfl γ h).1
  have hck : B.CkOn ⊤ (B.GV P.k (P.r - (j + 1))) (G t) := by
    intro γ₀ hγ₀
    obtain ⟨U, f, hU, hmem, hf, hfe⟩ := hG1 t ht γ₀ hγ₀
    have hcm : Continuous (fun γ : B.Mat P.k (P.r - (j + 1)) => (t, γ)) :=
      continuous_const.prodMk continuous_id
    refine ⟨(fun γ => (t, γ)) ⁻¹' U, fun γ => f (t, γ), hU.preimage hcm, hmem, ?_, ?_⟩
    · exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun γ hγ => hγ)
    · intro γ hγ hγG
      exact hfe (t, γ) hγ hγG
  exact ⟨ε, hε, hck, fun A' m' => JFxG.cptInCC_G hck hC (fun γ _ hγC => by
      by_contra h; exact hγC (hsupp γ h)) A' m', fun γ hγ hne => (hCε t rfl γ hne).2 hγ⟩

theorem representation_linear : RepLin := by
  intro Wp Wq _ _ _ _ _ _ P T _ _ j _ _ G G' hG hG' t ht a x hx
  obtain ⟨ε, hε, hN⟩ := repLin_nice T j G hG t ht
  obtain ⟨ε', hε', hN'⟩ := repLin_nice T j G' hG' t ht
  have hm : JC.NiceCoef (T.bs (j + 1)) (min ε ε') (G t) :=
    ⟨hN.1, hN.2.1, fun g hg hne => (min_le_left _ _).trans (hN.2.2 g hg hne)⟩
  have hm' : JC.NiceCoef (T.bs (j + 1)) (min ε ε') (G' t) :=
    ⟨hN'.1, hN'.2.1, fun g hg hne => (min_le_right _ _).trans (hN'.2.2 g hg hne)⟩
  have hom : wCell P.k (P.r - (j + 1)) (Fin.last (P.r - (j + 1))) x.1 * x.2 ∈
      JF.Om P.k (P.r - (j + 1)) (T.bs (j + 1)).z (T.bs (j + 1)).z' :=
    TLB.wCell_om (Pa := JC.parLev P (j + 1)) (T.bs (j + 1)) hx
  have hs : B.JF (T.bs (j + 1)) (fun γ => a • G t γ) = a • B.JF (T.bs (j + 1)) (G t) :=
    funext fun h => JCx2.bc_JF_smul a (G t) h
  refine ⟨?_, ?_⟩
  · simp only [resG]
    rw [JCx2.bc_JF_add hm hm' hom, smul_add]
  · rw [hs, JCx2.rma_resG_smul]

end Formalism.FourierDecayAlt.P.CutSH
end
end
