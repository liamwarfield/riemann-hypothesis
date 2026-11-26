module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.ExistsConj

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TransferOf
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.OneFormsMapOfFunctorMorphismSmul
noncomputable section

open Matrix Polynomial PositivityTheory.PfBern.Frob

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP.Desc.Piece.Tr PositivityTheory.RgUd.TP.Desc.Piece.PTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
  {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q) (τ : Fin D.m → ℕ)

theorem Continuous.cjc {X : Type*} [TopologicalSpace X] {f : X → GL (Fin N) k} {g : X → Matrix (Fin N) (Fin N) k}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => cj (f x) (g x) :=
  continuous_cj.comp (hf.prodMk hg)

theorem Continuous.actc {X : Type*} [TopologicalSpace X] {f : X → GL (Fin N) k} {g : X → Sp k N}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => act (f x) (g x) :=
  continuous_act.comp (hf.prodMk hg)

theorem Continuous.swc {X : Type*} [TopologicalSpace X] {f : X → Fin D.a0 → Matrix (Fin N) (Fin N) k}
    {g : X → Matrix (Fin N) (Fin N) k} (hf : Continuous f) (hg : Continuous g) : Continuous fun x => sw D (f x) (g x) := by
  refine continuous_pi fun j => ?_
  have h := (continuous_sw D j).comp (hf.prodMk hg)
  exact h

theorem Continuous.ewc {X : Type*} [TopologicalSpace X] {f : X → Fin D.a0 → Matrix (Fin N) (Fin N) k}
    {g : X → Matrix (Fin N) (Fin N) k} (hf : Continuous f) (hg : Continuous g) : Continuous fun x => ew D (f x) (g x) := by
  have h := (continuous_ew D).comp (hf.prodMk hg)
  exact h

def smulY (g : GL (Fin N) k) (p : Ys D τ) : Ys D τ := ⟨((fun i => cj g (p.1.1 i)), act g p.1.2), mem_Ys_cj D p.2 g⟩

theorem smulY_one (p : Ys D τ) : smulY D τ 1 p = p := by
  apply Subtype.ext
  simp [smulY, cj, act]

theorem smulY_mul (g h : GL (Fin N) k) (p : Ys D τ) : smulY D τ (g * h) p = smulY D τ g (smulY D τ h p) := by
  apply Subtype.ext
  simp [smulY, cj, act, _root_.mul_inv_rev, Matrix.mulVec_mulVec, mul_assoc]

instance actY : MulAction (GL (Fin N) k) (Ys D τ) where
  smul := smulY D τ
  one_smul := smulY_one D τ
  mul_smul := smulY_mul D τ

theorem smul_val (g : GL (Fin N) k) (p : Ys D τ) : (g • p).1 = ((fun i => cj g (p.1.1 i)), act g p.1.2) := rfl

instance continuousSMul_actY : ContinuousSMul (GL (Fin N) k) (Ys D τ) := by
  refine ⟨?_⟩
  have hv : Continuous fun p : GL (Fin N) k × Ys D τ => p.2.1 := continuous_subtype_val.comp continuous_snd
  have h : Continuous fun p : GL (Fin N) k × Ys D τ =>
      (((fun i => cj p.1 (p.2.1.1 i)), act p.1 p.2.1.2) : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N) :=
    (continuous_pi fun i => Continuous.cjc continuous_fst ((continuous_apply i).comp (continuous_fst.comp hv))).prodMk
      (Continuous.actc continuous_fst (continuous_snd.comp hv))
  exact h.subtype_mk fun p => mem_Ys_cj D p.2.2 p.1

variable {D τ}

theorem orb_of_Ys {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ Ys D τ) : p.1 ∈ Orb D.z := by
  obtain ⟨g, hg, -⟩ := hp
  exact ⟨g, hg⟩

theorem sw_of {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} {g : GL (Fin N) k} (hg : ∀ i, p.1 i = cj g (D.z i)) :
    sw D p.1 p.2.1 = fun j => cj g (pe (D.a j) (cj g⁻¹ p.2.1)) := by
  have hw : p.1 = fun i => cj g (D.z i) := funext hg
  funext j
  rw [hw]
  simp only [sw, lin_cj, lin_al]
  rw [← pe_cj, cj_cj_inv]

theorem ew_of {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} {g : GL (Fin N) k} (hg : ∀ i, p.1 i = cj g (D.z i)) :
    ew D p.1 p.2.1 = cj g (pe D.b (cj g⁻¹ p.2.1)) := by
  have hw : p.1 = fun i => cj g (D.z i) := funext hg
  rw [hw, ← eigenvalue_map_at_base, ← ew_cj, cj_cj_inv]

private theorem piece_inv_lemma {g : GL (Fin N) k} (hg : g ∈ Gz Z) {x : Matrix (Fin N) (Fin N) k}
    (hx : x ∈ piece D τ) : cj g x ∈ piece D τ := by
  unfold cj
  obtain ⟨hB, hχ, ht⟩ := hx
  refine ⟨PositivityTheory.RgUd.T.Desc.Asm.conj_mem_Bz hg hB, ?_, ?_⟩
  · rw [PositivityTheory.RgUd.TP.Desc.Piece.PTop.aeval_conj, hχ, mul_zero, zero_mul]
  · rw [← ht]
    funext t
    simp only [typ]
    have hc := fun j => PositivityTheory.RgUd.TP.Desc.Piece.PTop.pe_conj (D.a j) (D.ha j) hg x
    simp only [hc]
    rw [← PositivityTheory.RgUd.TP.Desc.Piece.PTop.rank_conj g (∑ j, D.κ t j • pe (D.a j) x)]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

private theorem re_cj_lemma_2 {d r : ℕ} (γ : Fin d → Fin r → k) (s : Fin r → Matrix (Fin N) (Fin N) k)
    (ε : Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) : re γ (fun j => cj g (s j)) (cj g ε) = cj g (re γ s ε) := by
  simp only [re, cj_sum, cj_smul, cj_mulM, cj_pow]

private theorem sw_cj_lemma_3 (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k)
    (g : GL (Fin N) k) : sw D (fun i => cj g (w i)) (cj g x) = fun j => cj g (sw D w x j) := by
  funext j
  simp only [sw, lin_cj, pe_cj]

theorem sw_mem_orb (hOH : OrbHom k) (hZ : CR Z) {x₀ : Matrix (Fin N) (Fin N) k} (hx₀ : x₀ ∈ piece D τ)
    {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ Ys D τ) :
    sw D p.1 p.2.1 ∈ Orb (fun j => pe (D.a j) x₀) := by
  obtain ⟨g, hg, hx⟩ := hp
  obtain ⟨h, hh⟩ := exists_isAttachedHodgeS_conj_mapRep D hOH hZ hx₀ hx
  refine ⟨g * h, fun j => ?_⟩
  rw [sw_of hg]
  show cj g (pe (D.a j) (cj g⁻¹ p.2.1)) = cj (g * h) (pe (D.a j) x₀)
  rw [hh j]
  simp only [cj, Units.val_mul, _root_.mul_inv_rev, mul_assoc]

theorem Ys_spec {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ Ys D τ) :
    (∀ j, sw D p.1 p.2.1 j * ew D p.1 p.2.1 = ew D p.1 p.2.1 * sw D p.1 p.2.1 j) ∧
      (∀ i, re (D.γ i) (sw D p.1 p.2.1) (ew D p.1 p.2.1) = p.1 i) ∧ re D.β (sw D p.1 p.2.1) (ew D p.1 p.2.1) = p.2.1 := by
  obtain ⟨g, hg, hx⟩ := hp
  obtain ⟨hB, hχ, -⟩ := hx
  have hs := D.spec _ hB hχ
  have h4 : ∀ j, pe (D.a j) (cj g⁻¹ p.2.1) * pe D.b (cj g⁻¹ p.2.1) =
      pe D.b (cj g⁻¹ p.2.1) * pe (D.a j) (cj g⁻¹ p.2.1) := hs.2.2.2.1
  have h7 : ∀ i, D.z i = re (D.γ i) (fun j => pe (D.a j) (cj g⁻¹ p.2.1)) (pe D.b (cj g⁻¹ p.2.1)) :=
    hs.2.2.2.2.2.2.1
  have h8 : cj g⁻¹ p.2.1 = re D.β (fun j => pe (D.a j) (cj g⁻¹ p.2.1)) (pe D.b (cj g⁻¹ p.2.1)) :=
    hs.2.2.2.2.2.2.2.1
  rw [sw_of hg, ew_of hg]
  refine ⟨fun j => ?_, fun i => ?_, ?_⟩
  · beta_reduce
    rw [← cj_mulM, ← cj_mulM, h4 j]
  · rw [re_cj_lemma_2, ← h7 i, hg i]
  · rw [re_cj_lemma_2, ← h8, cj_cj_inv]

theorem e_smul {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    {e : GL (Fin N) k ⧸ GzS S ≃ₜ Orb b} (he : ∀ g : GL (Fin N) k, ((e g : Orb b) : Fin r → _) = fun i => cj g (b i))
    (g : GL (Fin N) k) (c : GL (Fin N) k ⧸ GzS S) : ((e (g • c) : Orb b) : Fin r → _) = fun i => cj g ((e c).1 i) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
  rw [MulAction.Quotient.smul_mk, he, he]
  funext i
  simp [cj, _root_.mul_inv_rev, mul_assoc]

theorem e_eq_one_iff {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    {e : GL (Fin N) k ⧸ GzS S ≃ₜ Orb b} (he : ∀ g : GL (Fin N) k, ((e g : Orb b) : Fin r → _) = fun i => cj g (b i))
    (w : Orb b) : e.symm w = ((1 : GL (Fin N) k) : GL (Fin N) k ⧸ GzS S) ↔ w.1 = b := by
  rw [Homeomorph.symm_apply_eq, Subtype.ext_iff, he]
  have h1 : (fun i => cj (1 : GL (Fin N) k) (b i)) = b := by
    funext i
    simp [cj]
  rw [h1]

variable (D τ)

def p1 (e₁ : GL (Fin N) k ⧸ GzS Z ≃ₜ Orb D.z) (p : Ys D τ) : GL (Fin N) k ⧸ GzS Z := e₁.symm ⟨p.1.1, orb_of_Ys p.2⟩

def p2 (hOH : OrbHom k) (hZ : CR Z) {x₀ : Matrix (Fin N) (Fin N) k} (hx₀ : x₀ ∈ piece D τ)
    (e₂ : GL (Fin N) k ⧸ GzS (Sx D x₀) ≃ₜ Orb (fun j => pe (D.a j) x₀)) (p : Ys D τ) :
    GL (Fin N) k ⧸ GzS (Sx D x₀) :=
  e₂.symm ⟨sw D p.1.1 p.1.2.1, sw_mem_orb hOH hZ hx₀ p.2⟩

variable {D τ}

section E1

variable {e₁ : GL (Fin N) k ⧸ GzS Z ≃ₜ Orb D.z} (he₁ : ∀ g : GL (Fin N) k, ((e₁ g : Orb D.z) : Fin D.a0 → _) =
  fun i => cj g (D.z i))
include he₁

theorem oneFormsMapOfFunctorMorphism_smul (g : GL (Fin N) k) (p : Ys D τ) : p1 D τ e₁ (g • p) = g • p1 D τ e₁ p := by
  apply e₁.injective
  apply Subtype.ext
  rw [e_smul he₁]
  simp only [p1, Homeomorph.apply_symm_apply, smul_val]

theorem first_orbit_map_eq_one_iff (p : Ys D τ) : p1 D τ e₁ p = ((1 : GL (Fin N) k) : GL (Fin N) k ⧸ GzS Z) ↔ p.1.1 = D.z :=
  e_eq_one_iff he₁ _

theorem continuous_first_orbit_map : Continuous (p1 D τ e₁) :=
  e₁.symm.continuous.comp (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _)

theorem mem_piece_of_first_fibre (hZ : CR Z) (y : Fib (p1 D τ e₁)) : y.1.1.2 ∈ piece D τ ×ˢ (Set.univ : Set (Fin N → k)) := by
  obtain ⟨⟨p, hp⟩, hy⟩ := y
  have hz1 : p.1 = D.z := (first_orbit_map_eq_one_iff he₁ ⟨p, hp⟩).1 hy
  obtain ⟨g, hg, hx⟩ := hp
  have hgZ : g ∈ Gz Z := (mem_GzS_iff D.hz g).2 fun i => by rw [← hg i, hz1]
  refine ⟨?_, Set.mem_univ _⟩
  have h1 := piece_inv_lemma hgZ hx
  rw [cj_cj_inv] at h1
  exact h1

end E1

theorem mem_Ys_of_piece (y : piece D τ ×ˢ (Set.univ : Set (Fin N → k))) : (D.z, y.1) ∈ Ys D τ := by
  refine ⟨1, fun i => ?_, ?_⟩
  · simp [cj]
  · simpa [cj] using y.2.1

def hY1 (e₁ : GL (Fin N) k ⧸ GzS Z ≃ₜ Orb D.z) (he₁ : ∀ g : GL (Fin N) k, ((e₁ g : Orb D.z) : Fin D.a0 → _) =
    fun i => cj g (D.z i)) (hZ : CR Z) : Fib (p1 D τ e₁) ≃ₜ (piece D τ ×ˢ (Set.univ : Set (Fin N → k))) where
  toFun y := ⟨y.1.1.2, mem_piece_of_first_fibre he₁ hZ y⟩
  invFun y := ⟨⟨(D.z, y.1), mem_Ys_of_piece y⟩, (first_orbit_map_eq_one_iff he₁ _).2 rfl⟩
  left_inv y := Subtype.ext (Subtype.ext (Prod.ext ((first_orbit_map_eq_one_iff he₁ y.1).1 y.2).symm rfl))
  right_inv y := rfl
  continuous_toFun := Continuous.subtype_mk (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk (continuous_const.prodMk continuous_subtype_val) _) _

theorem first_fibre_homeomorph_smul {e₁ : GL (Fin N) k ⧸ GzS Z ≃ₜ Orb D.z} (he₁ : ∀ g : GL (Fin N) k, ((e₁ g : Orb D.z) : Fin D.a0 → _) =
    fun i => cj g (D.z i)) (hZ : CR Z) (h : GzS Z) (y : Fib (p1 D τ e₁)) :
    (hY1 e₁ he₁ hZ (fibSmul (oneFormsMapOfFunctorMorphism_smul he₁) h y)).1 = act h.1 (hY1 e₁ he₁ hZ y).1 := rfl

section E2

variable {hOH : OrbHom k} {hZ : CR Z} {x₀ : Matrix (Fin N) (Fin N) k} {hx₀ : x₀ ∈ piece D τ}
  {e₂ : GL (Fin N) k ⧸ GzS (Sx D x₀) ≃ₜ Orb (fun j => pe (D.a j) x₀)}
  (he₂ : ∀ g : GL (Fin N) k, ((e₂ g : Orb (fun j => pe (D.a j) x₀)) : Fin D.r → _) = fun j => cj g (pe (D.a j) x₀))
include he₂

theorem second_orbit_map_equivariant (g : GL (Fin N) k) (p : Ys D τ) : p2 D τ hOH hZ hx₀ e₂ (g • p) = g • p2 D τ hOH hZ hx₀ e₂ p := by
  apply e₂.injective
  apply Subtype.ext
  rw [e_smul he₂]
  simp only [p2, Homeomorph.apply_symm_apply, smul_val]
  exact sw_cj_lemma_3 p.1.1 p.1.2.1 g

theorem second_orbit_map_eq_one_iff (p : Ys D τ) : p2 D τ hOH hZ hx₀ e₂ p = ((1 : GL (Fin N) k) : GL (Fin N) k ⧸ GzS (Sx D x₀)) ↔
    sw D p.1.1 p.1.2.1 = fun j => pe (D.a j) x₀ := by
  unfold p2
  exact e_eq_one_iff he₂ _

omit he₂ in
theorem continuous_p2 : Continuous (p2 D τ hOH hZ hx₀ e₂) := by
  unfold p2
  exact e₂.symm.continuous.comp ((Continuous.swc D (continuous_fst.comp continuous_subtype_val)
    (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _)

end E2

def psi (D : SData Z χ q) (x₀ : Matrix (Fin N) (Fin N) k) (y : Sp k N) : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N :=
  ((fun i => re (D.γ i) (fun j => pe (D.a j) x₀) y.1), (re D.β (fun j => pe (D.a j) x₀) y.1, y.2))

theorem continuous_psi (x₀ : Matrix (Fin N) (Fin N) k) : Continuous (psi D x₀) :=
  (continuous_pi fun i => (continuous_re _ _).comp continuous_fst).prodMk
    (((continuous_re _ _).comp continuous_fst).prodMk continuous_snd)


variable (D τ) in
def Ys2 (x₀ : Matrix (Fin N) (Fin N) k) : Set (Sp k N) :=
  {y | psi D x₀ y ∈ Ys D τ ∧ sw D (psi D x₀ y).1 (psi D x₀ y).2.1 = (fun j => pe (D.a j) x₀) ∧
    ew D (psi D x₀ y).1 (psi D x₀ y).2.1 = y.1}

theorem isClosed_second_fibre_set (hOC : OrbClosed k) (hZ : CR Z) (x₀ : Matrix (Fin N) (Fin N) k) : IsClosed (Ys2 D τ x₀) := by
  have hYs := isClosed_Ys D hOC hZ τ fun g hg x hx => piece_inv_lemma hg hx
  refine (hYs.preimage (continuous_psi x₀)).inter ((isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_fst))
  · exact Continuous.swc D (continuous_fst.comp (continuous_psi x₀))
      (continuous_fst.comp (continuous_snd.comp (continuous_psi x₀)))
  · exact Continuous.ewc D (continuous_fst.comp (continuous_psi x₀))
      (continuous_fst.comp (continuous_snd.comp (continuous_psi x₀)))

theorem Ys2_sub {x₀ : Matrix (Fin N) (Fin N) k} (hB0 : x₀ ∈ Bz Z) (hχ0 : aeval x₀ χ = 0) {y : Sp k N}
    (hy : y ∈ Ys2 D τ x₀) : y ∈ Bz (Sx D x₀) ×ˢ (Set.univ : Set (Fin N → k)) := by
  obtain ⟨hY, hs, he⟩ := hy
  have hsp := (Ys_spec hY).1
  rw [hs, he] at hsp
  refine ⟨fun a ha => ?_, Set.mem_univ _⟩
  have hle : Sx D x₀ ≤ Subalgebra.centralizer k {y.1} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    refine (Subalgebra.mem_centralizer_iff k).2 ?_
    rintro _ rfl
    exact (hsp j).symm
  have h1 := (Subalgebra.mem_centralizer_iff k).1 (hle ha) y.1 rfl
  exact h1.symm

section E2b

variable {hOH : OrbHom k} {hZ : CR Z} {x₀ : Matrix (Fin N) (Fin N) k} {hx₀ : x₀ ∈ piece D τ}
  {e₂ : GL (Fin N) k ⧸ GzS (Sx D x₀) ≃ₜ Orb (fun j => pe (D.a j) x₀)}
  (he₂ : ∀ g : GL (Fin N) k, ((e₂ g : Orb (fun j => pe (D.a j) x₀)) : Fin D.r → _) = fun j => cj g (pe (D.a j) x₀))
include he₂

theorem psi_ew (y : Fib (p2 D τ hOH hZ hx₀ e₂)) :
    psi D x₀ (ew D y.1.1.1 y.1.1.2.1, y.1.1.2.2) = y.1.1 := by
  have hs := (second_orbit_map_eq_one_iff he₂ y.1).1 y.2
  obtain ⟨-, hz, hx⟩ := Ys_spec y.1.2
  rw [hs] at hz hx
  exact Prod.ext (funext hz) (Prod.ext hx rfl)

theorem mem_second_fibre_set_of_fib (y : Fib (p2 D τ hOH hZ hx₀ e₂)) : (ew D y.1.1.1 y.1.1.2.1, y.1.1.2.2) ∈ Ys2 D τ x₀ := by
  have hs : sw D y.1.1.1 y.1.1.2.1 = fun j => pe (D.a j) x₀ := (second_orbit_map_eq_one_iff he₂ y.1).1 y.2
  have h := psi_ew he₂ y
  refine ⟨?_, ?_, ?_⟩
  · rw [h]
    exact y.1.2
  · rw [h]
    exact hs
  · rw [h]

theorem second_fibre_of_set (y : Ys2 D τ x₀) : p2 D τ hOH hZ hx₀ e₂ ⟨psi D x₀ y.1, y.2.1⟩ = ((1 : GL (Fin N) k) : _ ⧸ _) :=
  (second_orbit_map_eq_one_iff he₂ _).2 y.2.2.1

end E2b

def hY2 {hOH : OrbHom k} {hZ : CR Z} {x₀ : Matrix (Fin N) (Fin N) k} {hx₀ : x₀ ∈ piece D τ}
    {e₂ : GL (Fin N) k ⧸ GzS (Sx D x₀) ≃ₜ Orb (fun j => pe (D.a j) x₀)}
    (he₂ : ∀ g : GL (Fin N) k, ((e₂ g : Orb (fun j => pe (D.a j) x₀)) : Fin D.r → _) = fun j => cj g (pe (D.a j) x₀)) :
    Fib (p2 D τ hOH hZ hx₀ e₂) ≃ₜ Ys2 D τ x₀ where
  toFun y := ⟨(ew D y.1.1.1 y.1.1.2.1, y.1.1.2.2), mem_second_fibre_set_of_fib he₂ y⟩
  invFun y := ⟨⟨psi D x₀ y.1, y.2.1⟩, second_fibre_of_set he₂ y⟩
  left_inv y := Subtype.ext (Subtype.ext (psi_ew he₂ y))
  right_inv y := Subtype.ext (Prod.ext y.2.2.2 rfl)
  continuous_toFun := by
    have hv : Continuous fun y : Fib (p2 D τ hOH hZ hx₀ e₂) => y.1.1 :=
      continuous_subtype_val.comp continuous_subtype_val
    exact ((Continuous.ewc D (continuous_fst.comp hv) (continuous_fst.comp (continuous_snd.comp hv))).prodMk
      (continuous_snd.comp (continuous_snd.comp hv))).subtype_mk _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk ((continuous_psi x₀).comp continuous_subtype_val) _) _

section CasimirPairingBound

variable {hOH : OrbHom k} {hZ : CR Z} {x₀ : Matrix (Fin N) (Fin N) k} {hx₀ : x₀ ∈ piece D τ}
  {e₂ : GL (Fin N) k ⧸ GzS (Sx D x₀) ≃ₜ Orb (fun j => pe (D.a j) x₀)}
  (he₂ : ∀ g : GL (Fin N) k, ((e₂ g : Orb (fun j => pe (D.a j) x₀)) : Fin D.r → _) = fun j => cj g (pe (D.a j) x₀))
include he₂

theorem second_fibre_homeomorph_val (y : Fib (p2 D τ hOH hZ hx₀ e₂)) : (hY2 he₂ y).1 = (ew D y.1.1.1 y.1.1.2.1, y.1.1.2.2) := rfl

theorem second_fibre_homeomorph_smul (h : GzS (Sx D x₀)) (y : Fib (p2 D τ hOH hZ hx₀ e₂)) :
    (hY2 he₂ (fibSmul (second_orbit_map_equivariant he₂) h y)).1 = act h.1 (hY2 he₂ y).1 := by
  rw [second_fibre_homeomorph_val, second_fibre_homeomorph_val]
  show (ew D (h.1 • y.1).1.1 (h.1 • y.1).1.2.1, (h.1 • y.1).1.2.2) = _
  rw [smul_val]
  exact Prod.ext (ew_cj D _ _ _) rfl

end CasimirPairingBound

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
end
end

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic MeasureTheory
open GroundTheory.Automorphic.Whittaker hiding pullL

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc.Piece.Tr PositivityTheory.RgUd.TP.Desc.Piece.PTop
open PositivityTheory.PfBern.Loc (SC restr restr_surjective pullL mulInd)
open PositivityTheory.PfBern.Frob (FrobeniusReciprocity IsUnimod eqvF translF Fib fibSmul)

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def actH {N : ℕ} (g : GL (Fin N) k) : Sp k N ≃ₜ Sp k N where
  toFun := act g
  invFun := act g⁻¹
  left_inv q := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv q := by rw [← act_mul, mul_inv_cancel, act_one]
  continuous_toFun := Continuous.actc continuous_const continuous_id
  continuous_invFun := Continuous.actc continuous_const continuous_id

set_option maxHeartbeats 1000000 in
theorem transfer_of : (PositivityTheory.PfBern.Frob.FrobeniusReciprocity → DoubleTransfer) → OrbHom k → OrbClosed k → Transfer k := by
  intro hDT hOH hOC hFr p _ _ hU N q Z hZ χ D τ x₀ hx₀ hV ξ hsupp hinv f hf
  haveI : T2Space k := t2k
  haveI : TotallyDisconnectedSpace k := tdk
  haveI : SecondCountableTopology k := sck
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) := tdM
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) k) := inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → k))
  haveI : SecondCountableTopology (GL (Fin N) k) := GlobalTheory.SplitFlip.secondCountable_GL
  letI : MeasurableSpace (GL (Fin N) k) := borel _
  haveI : BorelSpace (GL (Fin N) k) := ⟨rfl⟩
  have hP := pieceTop k N q Z hZ χ D τ
  have hCR : CR (Sx D x₀) := hP.2.2 x₀ hx₀
  have hB0 : x₀ ∈ Bz Z := hx₀.1
  have hχ0 : aeval x₀ χ = 0 := hx₀.2.1
  obtain ⟨e₁, he₁⟩ := exists_orb_homeo hOC hZ D.hz
  obtain ⟨e₂, he₂⟩ := exists_orb_homeo hOC hCR (sx_span D hB0 hχ0)
  have hYc : IsClosed (Ys D τ) := isClosed_Ys D hOC hZ τ hP.2.1
  haveI : LocallyCompactSpace (Ys D τ) := hYc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have hp₁ := oneFormsMapOfFunctorMorphism_smul (τ := τ) he₁
  have hp₂ := second_orbit_map_equivariant (τ := τ) (hOH := hOH) (hZ := hZ) (hx₀ := hx₀) he₂
  let C : Set (Ys D τ) := {y | y.1.2.2 = 0}
  have hCc : IsClosed C := isClosed_eq (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)) continuous_const
  have hCinv : ∀ (g : GL (Fin N) k), ∀ y ∈ C, g • y ∈ C := by
    intro g y hy
    change g.val *ᵥ y.1.2.2 = 0
    rw [show y.1.2.2 = 0 from hy, Matrix.mulVec_zero]

  have hyp : ∀ E ∈ eqvF hp₂ ((1 : GL (Fin N) k →* ℂˣ).comp (GzS (Sx D x₀)).subtype),
      PositivityTheory.PfBern.Frob.SupportedIn E (Subtype.val ⁻¹' C) := by
    intro E hEeqv φ0 hφ0
    let hY := hY2 (hOH := hOH) (hZ := hZ) (hx₀ := hx₀) he₂
    have hY2c : IsClosed (Ys2 D τ x₀) := isClosed_second_fibre_set hOC hZ x₀
    let E' : PositivityTheory.PfBern.Loc.Distr (Ys2 D τ x₀) := E.comp (pullL hY)
    obtain ⟨η, hη⟩ := exists_functional hY2c E'
    have hSη : Supp η (Bz (Sx D x₀) ×ˢ Set.univ) := by
      intro f hf1 hvan
      have hr : restr hY2c ⟨f, hf1.1⟩ = 0 := Subtype.ext (funext fun y => hvan y.1 (Ys2_sub hB0 hχ0 y.2))
      have := hη ⟨f, hf1.1⟩
      rw [hr, map_zero] at this
      exact this
    have hIη : Inv (Sx D x₀) η := by
      intro h hh f hf1
      let hH : GzS (Sx D x₀) := ⟨h, hh⟩
      let f1 : SC (Sp k N) := pullL (actH k h) ⟨f, hf1.1⟩
      have key : pullL hY (restr hY2c f1) = translF hp₂ hH⁻¹ (pullL hY (restr hY2c ⟨f, hf1.1⟩)) := by
        apply Subtype.ext
        funext z
        change f (act h (hY z).1) = f (hY (fibSmul hp₂ hH⁻¹⁻¹ z)).1
        rw [second_fibre_homeomorph_smul he₂, inv_inv]
      have h1 : η (fun q => f (act h q)) = η f1 := rfl
      rw [h1, hη f1, hη ⟨f, hf1.1⟩]
      change E (pullL hY (restr hY2c f1)) = E (pullL hY (restr hY2c ⟨f, hf1.1⟩))
      rw [key]
      exact (hEeqv hH⁻¹ _).trans (by simp)
    have hkill := hV η hSη hIη
    let φ' : SC (Ys2 D τ x₀) := pullL hY.symm φ0
    obtain ⟨f0, hf0⟩ := restr_surjective hY2c φ'
    have hsupp' : Function.support (φ' : Ys2 D τ x₀ → ℂ) ⊆ {y | y.1.2 ≠ 0} := fun y hy => hφ0 hy
    have hK : IsCompact (Subtype.val '' Function.support (φ' : Ys2 D τ x₀ → ℂ)) :=
      (isCompact_support φ'.2).image continuous_subtype_val
    have hKsub : Subtype.val '' Function.support (φ' : Ys2 D τ x₀ → ℂ) ⊆ {q : Sp k N | q.2 ≠ 0} := by
      rintro _ ⟨y, hy, rfl⟩
      exact hsupp' hy
    have hUo : IsOpen {q : Sp k N | q.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
    obtain ⟨Bc, hBc, hBo, hKB, hBU⟩ := exists_isCompact_isOpen_between hK hUo hKsub
    let f : SC (Sp k N) := mulInd Bc ⟨hBc.isClosed, hBo⟩ f0
    have hrf : restr hY2c f = φ' := by
      apply Subtype.ext
      funext y
      change Bc.indicator 1 y.1 * (f0 : Sp k N → ℂ) y.1 = (φ' : Ys2 D τ x₀ → ℂ) y
      have e0 : (f0 : Sp k N → ℂ) y.1 = (φ' : Ys2 D τ x₀ → ℂ) y := congrFun (congrArg Subtype.val hf0) y
      by_cases hyB : y.1 ∈ Bc
      · simp [hyB, e0]
      · have : (φ' : Ys2 D τ x₀ → ℂ) y = 0 := by
          by_contra hne
          exact hyB (hKB ⟨y, hne, rfl⟩)
        simp [hyB, this]
    have hfU : (f : Sp k N → ℂ) ∈ supportedIn {q : Sp k N | q.2 ≠ 0} := by
      refine ⟨f.2, fun q hq => hBU ?_⟩
      by_contra hqB
      exact hq (by simp [f, mulInd, hqB])
    have hz := hkill f hfU
    rw [hη f, hrf] at hz
    have e2 : pullL hY φ' = φ0 := PositivityTheory.PfBern.Loc.pullL_pullL_symm hY φ0
    change E (pullL hY φ') = 0 at hz
    rw [e2] at hz
    exact hz

  have hPc : IsClosed (piece D τ ×ˢ (Set.univ : Set (Fin N → k))) := hP.1.prod isClosed_univ
  obtain ⟨Dd, hDd⟩ := exists_distr_on ξ hPc hsupp
  let hY1' := hY1 (τ := τ) e₁ he₁ hZ
  let E₁ : PositivityTheory.PfBern.Frob.Distr (Fib (p1 D τ e₁)) := Dd.comp (pullL hY1'.symm)
  have hE₁ : E₁ ∈ eqvF hp₁ ((1 : GL (Fin N) k →* ℂˣ).comp (GzS Z).subtype) := by
    intro h φ
    obtain ⟨f0, hf0⟩ := restr_surjective hPc (pullL hY1'.symm φ)
    have hφ : ∀ w, (φ : Fib (p1 D τ e₁) → ℂ) w = (f0 : Sp k N → ℂ) (hY1' w).1 := fun w => by
      have := congrFun (congrArg Subtype.val hf0) (hY1' w)
      change (f0 : Sp k N → ℂ) (hY1' w).1 = (φ : Fib (p1 D τ e₁) → ℂ) (hY1'.symm (hY1' w)) at this
      rw [Homeomorph.symm_apply_apply] at this
      exact this.symm
    let f1 : SC (Sp k N) := pullL (actH k (h⁻¹).1) f0
    have e1 : pullL hY1'.symm (translF hp₁ h φ) = restr hPc f1 := by
      apply Subtype.ext
      funext y
      change (φ : Fib (p1 D τ e₁) → ℂ) (fibSmul hp₁ h⁻¹ (hY1'.symm y)) = (f0 : Sp k N → ℂ) (act (h⁻¹).1 y.1)
      rw [hφ, first_fibre_homeomorph_smul he₁ hZ, Homeomorph.apply_symm_apply]
    simp only [MonoidHom.comp_apply, MonoidHom.one_apply, Units.val_one, one_mul]
    change Dd (pullL hY1'.symm (translF hp₁ h φ)) = Dd (pullL hY1'.symm φ)
    rw [e1, ← hf0, ← hDd f1, ← hDd f0]
    exact hinv (h⁻¹).1 (h⁻¹).2 f0 ⟨f0.2, Set.subset_univ _⟩
  have hSupp := hDT hFr (GL (Fin N) k) (GzS Z) (GzS (Sx D x₀)) (isClosed_GzS Z) (isClosed_GzS _) (isUnimod_GL hU)
    (hU N Z hZ) (hU N _ hCR) (Ys D τ) (p1 D τ e₁) (p2 D τ hOH hZ hx₀ e₂) (continuous_first_orbit_map he₁) continuous_p2 hp₁ hp₂
    C hCc hCinv hyp E₁ hE₁
  have hz := hSupp (pullL hY1' (restr hPc ⟨f, hf.1⟩)) fun w hw hwC => hw (by
    change f w.1.1.2 = 0
    by_contra hne
    exact hf.2 hne hwC)
  rw [show ξ f = Dd (restr hPc ⟨f, hf.1⟩) from hDd ⟨f, hf.1⟩,
    ← PositivityTheory.PfBern.Loc.pullL_pullL_symm hY1'.symm (restr hPc ⟨f, hf.1⟩)]
  exact hz

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.DoubleTransfer
noncomputable section

open PositivityTheory.PfBern.Frob PositivityTheory.RgUd.TP.Desc.Piece.Tr

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrDbl

theorem doubleTransfer : FrobeniusReciprocity → DoubleTransfer := by
  intro hF G _ _ _ _ _ _ _ _ _ H₁ H₂ _ _ hH₁ hH₂ hG hU₁ hU₂ X _ _ _ _ _ _ p₁ p₂ hc₁ hc₂ hp₁ hp₂ C hC hCinv hE₂ E hE
  obtain ⟨Fr₁, hs₁, -⟩ := hF G H₁ hH₁ hG hU₁ X p₁ hc₁ hp₁ 1 continuous_const
    (MeasureTheory.Measure.haar) (MeasureTheory.Measure.haar)
  obtain ⟨Fr₂, hs₂, -⟩ := hF G H₂ hH₂ hG hU₂ X p₂ hc₂ hp₂ 1 continuous_const
    (MeasureTheory.Measure.haar) (MeasureTheory.Measure.haar)
  set ξ := Fr₁.symm ⟨E, hE⟩
  have h2 : SupportedIn (↑ξ) C := (hs₂ ξ C hC hCinv).2 (hE₂ _ (Fr₂ ξ).2)
  have h1 := (hs₁ ξ C hC hCinv).1 h2
  simpa [ξ] using h1

end PositivityTheory.RgUd.TP.Desc.Piece.TrDbl
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.OrbClosed
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TrOrbB
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TrOrbA
noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb

universe u

theorem exists_equiv_of_torsion {k A : Type*} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    (I : Ideal A) [I.IsMaximal] (M M' : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M'] [FiniteDimensional k M]
    [FiniteDimensional k M'] (hM : Module.IsTorsionBySet A M I) (hM' : Module.IsTorsionBySet A M' I)
    (h : finrank k M = finrank k M') : Nonempty (M ≃ₗ[A] M') := by
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  letI := hM.module
  letI := hM'.module
  have tw : ∀ (P : Type u) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
      (hP : Module.IsTorsionBySet A P I), @IsScalarTower k (A ⧸ I) P _ hP.module.toSMul _ := by
    intro P _ _ _ _ hP
    letI := hP.module
    refine ⟨fun c x m => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hP.mk_smul, hP.mk_smul, mul_smul,
      algebraMap_smul]
  haveI := tw M hM
  haveI := tw M' hM'
  haveI : Module.Finite (A ⧸ I) M := Module.Finite.of_restrictScalars_finite k (A ⧸ I) M
  haveI : Module.Finite (A ⧸ I) M' := Module.Finite.of_restrictScalars_finite k (A ⧸ I) M'
  have h1 := Module.finrank_mul_finrank k (A ⧸ I) M
  have h2 := Module.finrank_mul_finrank k (A ⧸ I) M'
  have hpos : 0 < finrank k (A ⧸ I) := Module.finrank_pos
  have hK : finrank (A ⧸ I) M = finrank (A ⧸ I) M' := Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, h2, h])
  let T := LinearEquiv.ofFinrankEq M M' hK
  refine ⟨{ toFun := T
            map_add' := T.map_add
            map_smul' := fun a m => ?_
            invFun := T.symm
            left_inv := T.left_inv
            right_inv := T.right_inv }⟩
  show T (a • m) = a • T m
  rw [← hM.mk_smul, T.map_smul, hM'.mk_smul]


open Classical in
def pidem (A : Type*) [CommRing A] [IsArtinianRing A] [IsReduced A] (I : MaximalSpectrum A) : A :=
  by
    classical
    exact (IsArtinianRing.equivPi A).symm (Pi.single I 1)

section idem
open Classical
variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A]

theorem equivPi_pidem (I J : MaximalSpectrum A) :
    IsArtinianRing.equivPi A (pidem A I) J = Pi.single (M := fun I : MaximalSpectrum A => A ⧸ I.asIdeal) I 1 J := by
  rw [pidem, AlgEquiv.apply_symm_apply]

theorem pidem_mul (I J : MaximalSpectrum A) : pidem A I * pidem A J = if I = J then pidem A I else 0 := by
  apply (IsArtinianRing.equivPi A).injective
  funext L
  split_ifs with h
  · subst h
    rw [map_mul, Pi.mul_apply, equivPi_pidem]
    by_cases hL : L = I
    · subst hL; simp
    · simp [Pi.single_apply, hL]
  · rw [map_mul, Pi.mul_apply, equivPi_pidem, equivPi_pidem, map_zero, Pi.zero_apply]
    by_cases hL : L = I
    · subst hL; simp [Pi.single_apply, Ne.symm h]
    · simp [Pi.single_apply, hL]

theorem pidem_idem (I : MaximalSpectrum A) : IsIdempotentElem (pidem A I) := by
  have h := pidem_mul I I
  rw [if_pos rfl] at h
  exact h

theorem sum_pidem [Fintype (MaximalSpectrum A)] : ∑ I, pidem A I = 1 := by
  apply (IsArtinianRing.equivPi A).injective
  funext L
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply, map_one, Pi.one_apply]
  simp_rw [equivPi_pidem]
  simp [Pi.single_apply]

theorem mul_pidem_of_mem (I : MaximalSpectrum A) {x : A} (hx : x ∈ I.asIdeal) : x * pidem A I = 0 := by
  apply (IsArtinianRing.equivPi A).injective
  funext L
  rw [map_mul, Pi.mul_apply, equivPi_pidem, map_zero, Pi.zero_apply]
  by_cases hL : L = I
  · subst hL
    rw [IsArtinianRing.equivPi_apply, (Ideal.Quotient.eq_zero_iff_mem).2 hx, zero_mul]
  · simp [Pi.single_apply, hL]

end idem

def piece {A : Type*} (M : Type*) [CommRing A] [AddCommGroup M] [Module A M] (e : A) : Submodule A M :=
  LinearMap.range (LinearMap.lsmul A M e)

section dec
open Classical
variable {A : Type*} [CommRing A] [IsArtinianRing A] [IsReduced A] [Fintype (MaximalSpectrum A)]

theorem pidem_smul_piece (P : Type*) [AddCommGroup P] [Module A P] (I J : MaximalSpectrum A) {y : P}
    (hy : y ∈ piece P (pidem A I)) : pidem A J • y = if J = I then y else 0 := by
  obtain ⟨m, rfl⟩ := hy
  rw [LinearMap.lsmul_apply, smul_smul, pidem_mul]
  split_ifs with h
  · subst h; rfl
  · exact zero_smul A m

def decomp (P : Type*) [AddCommGroup P] [Module A P] : P ≃ₗ[A] ∀ I : MaximalSpectrum A, piece P (pidem A I) where
  toFun m I := ⟨pidem A I • m, m, rfl⟩
  map_add' m m' := by funext I; ext; simp [smul_add]
  map_smul' a m := by funext I; ext; simp [smul_comm (pidem A I) a m]
  invFun x := ∑ I, (x I : P)
  left_inv m := by
    simp only
    rw [← Finset.sum_smul, sum_pidem, one_smul]
  right_inv x := by
    funext J
    ext
    simp only [Finset.smul_sum]
    rw [Finset.sum_eq_single J]
    · rw [pidem_smul_piece P J J (x J).2, if_pos rfl]
    · intro I _ hI
      rw [pidem_smul_piece P I J (x I).2, if_neg (Ne.symm hI)]
    · intro h; exact absurd (Finset.mem_univ J) h

end dec

theorem exists_equiv_of_finrank {k A : Type*} [Field k] [CommRing A] [Algebra k A] [FiniteDimensional k A]
    [IsReduced A] (M M' : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
    [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M'] [FiniteDimensional k M]
    [FiniteDimensional k M']
    (h : ∀ e : A, IsIdempotentElem e → finrank k (piece M e) = finrank k (piece M' e)) :
    Nonempty (M ≃ₗ[A] M') := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have tor : ∀ (P : Type u) [AddCommGroup P] [Module A P] (I : MaximalSpectrum A),
      Module.IsTorsionBySet A (piece P (pidem A I)) I.asIdeal := by
    intro P _ _ I y a
    obtain ⟨y, m, rfl⟩ := y
    ext
    simp [smul_smul, mul_pidem_of_mem I a.2]
  have fd : ∀ (P : Type u) [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
      [FiniteDimensional k P] (e : A), FiniteDimensional k (piece P e) := fun P _ _ _ _ _ e =>
    Module.Finite.of_injective ((piece P e).subtype.restrictScalars k) Subtype.val_injective
  have T : ∀ I : MaximalSpectrum A, Nonempty (piece M (pidem A I) ≃ₗ[A] piece M' (pidem A I)) := fun I =>
    haveI := fd M (pidem A I)
    haveI := fd M' (pidem A I)
    exists_equiv_of_torsion I.asIdeal _ _ (tor M I) (tor M' I) (h _ (pidem_idem I))
  exact ⟨(decomp M).trans ((LinearEquiv.piCongrRight fun I => (T I).some).trans (decomp M').symm)⟩

section rep
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] {N : ℕ}

@[nolint unusedArguments]
def Rep (_ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k) : Type _ := Fin N → k

variable (ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k)

instance : AddCommGroup (Rep ρ) := inferInstanceAs (AddCommGroup (Fin N → k))
instance : Module k (Rep ρ) := inferInstanceAs (Module k (Fin N → k))
instance : FiniteDimensional k (Rep ρ) := inferInstanceAs (FiniteDimensional k (Fin N → k))
instance : Module A (Rep ρ) :=
  Module.compHom (Fin N → k) ((Matrix.toLinAlgEquiv' (R := k) (n := Fin N)).toAlgHom.comp ρ).toRingHom

theorem rep_smul (a : A) (v : Rep ρ) : a • v = (ρ a *ᵥ (v : Fin N → k) : Fin N → k) := rfl

instance : IsScalarTower k A (Rep ρ) := ⟨fun c a v => by
  rw [rep_smul, rep_smul, map_smul]
  exact Matrix.smul_mulVec _ _ _⟩

theorem finrank_piece_rep (e : A) : finrank k (piece (Rep ρ) e) = (ρ e).rank := by
  have hs : ((piece (Rep ρ) e).restrictScalars k : Submodule k (Fin N → k)) =
      LinearMap.range (ρ e).mulVecLin := by
    ext v
    simp only [Submodule.restrictScalars_mem, piece, LinearMap.mem_range, LinearMap.lsmul_apply,
      Matrix.mulVecLin_apply]
    rfl
  rw [Matrix.rank, ← hs]
  rfl

end rep

theorem orbHom_gen (k : Type*) [Field k] (N : ℕ) (A : Type*) [CommRing A] [Algebra k A] [FiniteDimensional k A]
    (hA : IsReduced A) (ρ ρ' : A →ₐ[k] Matrix (Fin N) (Fin N) k)
    (h : ∀ e : A, IsIdempotentElem e → (ρ e).rank = (ρ' e).rank) :
    ∃ g : GL (Fin N) k, ∀ a, ρ' a = g.val * ρ a * g⁻¹.val := by
  obtain ⟨F⟩ := exists_equiv_of_finrank (k := k) (A := A) (Rep ρ) (Rep ρ') fun e he => by
    rw [finrank_piece_rep, finrank_piece_rep, h e he]
  let f : (Fin N → k) ≃ₗ[k] (Fin N → k) := F.restrictScalars k
  have hf : ∀ a v, f (ρ a *ᵥ v) = ρ' a *ᵥ f v := fun a v => F.map_smul a v
  let g : GL (Fin N) k := ⟨LinearMap.toMatrix' f.toLinearMap, LinearMap.toMatrix' f.symm.toLinearMap, by
      rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]; congr 1; ext v; simp, by
      rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]; congr 1; ext v; simp⟩
  refine ⟨g, fun a => ?_⟩
  have hc : ρ' a * g.val = g.val * ρ a := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
    show Matrix.toLin' (ρ' a) ∘ₗ Matrix.toLin' (LinearMap.toMatrix' f.toLinearMap) =
      Matrix.toLin' (LinearMap.toMatrix' f.toLinearMap) ∘ₗ Matrix.toLin' (ρ a)
    rw [Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact (hf a v).symm
  calc ρ' a = ρ' a * (g.val * g⁻¹.val) := by rw [Units.mul_inv, mul_one]
    _ = g.val * ρ a * g⁻¹.val := by rw [← mul_assoc, hc]

end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
end
end

noncomputable section

open Matrix Module

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb

variable {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {N : ℕ}

theorem rank_eq_of_idem {R : Type*} [Field R] {P Q : Matrix (Fin N) (Fin N) R} (hP : P * P = P) (hQ : Q * Q = Q)
    (hu : IsUnit (Q * P + (1 - Q) * (1 - P)).det) : P.rank = Q.rank := by
  set u := Q * P + (1 - Q) * (1 - P)
  have h1 : u * P = Q * P := by
    simp only [u, add_mul, mul_assoc, sub_mul, one_mul, hP, sub_self, mul_zero, add_zero]
  have h2 : Q * u = Q * P := by
    simp only [u, mul_add, ← mul_assoc, mul_sub, mul_one, hQ, sub_self, zero_mul, add_zero]
  have : (u * P).rank = (Q * u).rank := by rw [h1, h2]
  rwa [rank_mul_eq_right_of_isUnit_det u P hu, rank_mul_eq_left_of_isUnit_det u Q hu] at this

theorem isClosed_idem_rank (n : ℕ) : IsClosed {P : Matrix (Fin N) (Fin N) k | P * P = P ∧ P.rank = n} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro Q hQ
  by_cases hi : Q * Q = Q
  · have hr : Q.rank ≠ n := fun h => hQ ⟨hi, h⟩
    refine ⟨{P | (Q * P + (1 - Q) * (1 - P)).det ≠ 0}, fun P hP hP' => hr ?_, ?_, ?_⟩
    · rw [← hP'.2]
      exact (rank_eq_of_idem hP'.1 hi (isUnit_iff_ne_zero.2 hP)).symm
    · exact isOpen_ne_fun (((continuous_const.mul continuous_id).add
        (continuous_const.mul (continuous_const.sub continuous_id))).matrix_det) continuous_const
    · show (Q * Q + (1 - Q) * (1 - Q)).det ≠ 0
      have : Q * Q + (1 - Q) * (1 - Q) = 1 := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, hi]; abel
      rw [this, det_one]; exact one_ne_zero
  · exact ⟨{P | P * P ≠ P}, fun P hP hP' => hP hP'.1, isOpen_ne_fun (continuous_id.mul continuous_id) continuous_id,
      hi⟩

theorem orbClosed_gen (N r : ℕ) (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (hA : IsReduced A)
    (b : Fin r → A) (hb : Submodule.span k (Set.range b) = ⊤) (ρ₀ : A →ₐ[k] Matrix (Fin N) (Fin N) k) :
    IsClosed {w : Fin r → Matrix (Fin N) (Fin N) k | ∃ g : GL (Fin N) k, ∀ i, w i = g.val * ρ₀ (b i) * g⁻¹.val} := by
  classical
  let L : (Fin r → k) → A := fun c => ∑ i, c i • b i
  let Φ : (Fin r → Matrix (Fin N) (Fin N) k) → (Fin r → k) → Matrix (Fin N) (Fin N) k :=
    fun w c => ∑ i, c i • w i
  have hL : ∀ a, ∃ c, L c = a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun k).1 (hb ▸ Submodule.mem_top)
  choose s hs using hL
  have Lsub : ∀ c c', L (c - c') = L c - L c' := fun c c' => by
    simp only [L, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have Φsub : ∀ w c c', Φ w (c - c') = Φ w c - Φ w c' := fun w c c' => by
    simp only [Φ, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have Φadd : ∀ w c c', Φ w (c + c') = Φ w c + Φ w c' := fun w c c' => by
    simp only [Φ, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have Φsmul : ∀ w (t : k) c, Φ w (t • c) = t • Φ w c := fun w t c => by
    simp only [Φ, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have Lsingle : ∀ i, L (Pi.single i 1) = b i := fun i => by
    simp [L, Pi.single_apply]
  have Φsingle : ∀ w i, Φ w (Pi.single i 1) = w i := fun w i => by
    simp [Φ, Pi.single_apply]
  have hΦc : ∀ c : Fin r → k, Continuous fun w : Fin r → Matrix (Fin N) (Fin N) k => Φ w c := fun c =>
    continuous_finsetSum _ fun i _ => (continuous_apply i).const_smul (c i)
  let S : Set (Fin r → Matrix (Fin N) (Fin N) k) :=
    (⋂ c, ⋂ (_ : L c = 0), {w | Φ w c = 0}) ∩ ((⋂ a, ⋂ a', {w | Φ w (s (a * a')) = Φ w (s a) * Φ w (s a')}) ∩
      ({w | Φ w (s 1) = 1} ∩ ⋂ e, ⋂ (_ : IsIdempotentElem e),
        (fun w => Φ w (s e)) ⁻¹' {P | P * P = P ∧ P.rank = (ρ₀ e).rank}))
  have hS : IsClosed S := by
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · exact isClosed_iInter fun c => isClosed_iInter fun _ => isClosed_eq (hΦc c) continuous_const
    · exact isClosed_iInter fun a => isClosed_iInter fun a' =>
        isClosed_eq (hΦc _) ((hΦc _).mul (hΦc _))
    · exact isClosed_eq (hΦc _) continuous_const
    · exact isClosed_iInter fun e => isClosed_iInter fun _ =>
        (isClosed_idem_rank (ρ₀ e).rank).preimage (hΦc (s e))
  convert hS using 1
  ext w
  simp only [S, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨g, hg⟩
    have hΦ : ∀ c, Φ w c = g.val * ρ₀ (L c) * g⁻¹.val := fun c => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Φ, L, hg, map_sum, map_smul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    have hgi : g⁻¹.val * g.val = 1 := Units.inv_mul g
    refine ⟨fun c hc => by rw [hΦ, hc, map_zero, mul_zero, zero_mul], fun a a' => ?_, ?_, fun e he => ?_⟩
    · rw [hΦ, hΦ, hΦ, hs, hs, hs, map_mul]
      simp only [mul_assoc]
      rw [← mul_assoc g⁻¹.val g.val, hgi, one_mul]
    · rw [hΦ, hs, map_one, mul_one, Units.mul_inv]
    · rw [hΦ, hs]
      refine ⟨?_, ?_⟩
      · have := congrArg ρ₀ he.eq
        rw [map_mul] at this
        simp only [mul_assoc]
        rw [← mul_assoc g⁻¹.val g.val, hgi, one_mul, ← mul_assoc (ρ₀ e), this]
      · rw [rank_mul_eq_left_of_isUnit_det _ _ (isUnits_det_units g⁻¹),
          rank_mul_eq_right_of_isUnit_det _ _ (isUnits_det_units g)]
  · rintro ⟨h0, hmul, h1, hrk⟩
    have hwd : ∀ c c', L c = L c' → Φ w c = Φ w c' := fun c c' h => by
      have := h0 (c - c') (by rw [Lsub, h, sub_self])
      rwa [Φsub, sub_eq_zero] at this
    let ρl : A →ₗ[k] Matrix (Fin N) (Fin N) k :=
      { toFun := fun a => Φ w (s a)
        map_add' := fun a a' => by
          rw [← Φadd]; apply hwd; rw [hs]
          simp only [L, Pi.add_apply, add_smul, Finset.sum_add_distrib]
          rw [show (∑ i, s a i • b i) = L (s a) from rfl, show (∑ i, s a' i • b i) = L (s a') from rfl, hs, hs]
        map_smul' := fun t a => by
          rw [RingHom.id_apply, ← Φsmul]; apply hwd; rw [hs]
          simp only [L, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
          rw [show (∑ i, s a i • b i) = L (s a) from rfl, hs] }
    let ρ : A →ₐ[k] Matrix (Fin N) (Fin N) k := AlgHom.ofLinearMap ρl h1 hmul
    have hρ : ∀ a, ρ a = Φ w (s a) := fun _ => rfl
    obtain ⟨g, hg⟩ := orbHom_gen k N A hA ρ₀ ρ fun e he => by rw [hρ, (hrk e he).2]
    refine ⟨g, fun i => ?_⟩
    rw [← hg, hρ, ← Φsingle w i]
    apply hwd
    rw [hs, Lsingle]

end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
end
end

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbHom : Tr.OrbHom k := fun N A _ _ _ hA ρ ρ' h => orbHom_gen k N A hA ρ ρ' h

theorem orbClosed : Tr.OrbClosed k := fun N r A _ _ _ hA b hb ρ₀ => orbClosed_gen N r A hA b hb ρ₀

end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
end

namespace PositivityTheory.RgUd.TP.Desc.Piece.PTr

open PositivityTheory.RgUd.TP.Desc.Piece

theorem transfer (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Transfer k :=
  TrI.transfer_of k TrDbl.doubleTransfer (TrOrb.orbHom k) (TrOrb.orbClosed k)

end PositivityTheory.RgUd.TP.Desc.Piece.PTr
