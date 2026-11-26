module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSPointwise

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASectionCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def SARadSec : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
      ∀ U : M.Ty P → MA.SmQ P.r P.TT, ∃ Φ ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ q : MA.Qp P.r P.TT,
        Φ q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
          (((Real.sqrt (MA.wq P.k q.1 P.TT))⁻¹ : ℝ) : ℂ) • ∑ ρ, (U ρ : MA.Qp P.r P.TT → ℂ) q • e ρ q.1.2

def SADescend : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → ∀ Φ ∈ Q.RadSp k r z z' π π',
      ∃ D₀ : Set (Q.Mx k r), Q.IsDom k r z z' 0 D₀ ∧ ∃ K ∈ Q.FFl k r z z' π π' 0 D₀,
        ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), 0 < Q.GGl k r z z' g →
          Q.wCell k r (Fin.last r) c * g ∈ D₀ ∧ K (Q.wCell k r (Fin.last r) c * g) = Φ c g

def SACover : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' →
    ∀ g ∈ Q.Glev k r 0 ∩ Q.OmPlus k r z z', ∃ n ∈ Q.Nlev k r 0, ∃ n' ∈ Q.Nlev k r 0, ∃ c ∈ OmX r,
      ∃ g₁ ∈ Q.Glev k r (Fin.last r), 0 < Q.GGl k r z z' g₁ ∧ g = n * (Q.wCell k r (Fin.last r) c * g₁) * n'

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SelfAdjointDescentHolds
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecDesc
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

open Formalism.FourierDecayAlt.P.Qx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section fam

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ}

def EqvL (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (J : Mx k r → (Wq →L[ℂ] Wp)) : Prop :=
  LeftEq k r z i D J ∧ RightEq k r z' i D J ∧
    ∀ g ∈ Glev k r i ∩ D, ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', J (h * g * h') = (π h).comp ((J g).comp (π' h'))

def FamD (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (D : Set (Mx k r)) (Φ : Fn k r (Wq →L[ℂ] Wp)) : Prop :=
  (∀ c ∈ OmX r, EqvL z z' π π' i D (Φ c)) ∧
  ∀ c₀ ∈ OmX r, ∀ g₀ ∈ Glev k r i ∩ D, ∃ (U : Set ((Fin r → ℂ) × Mx k r)) (F : (Fin r → ℂ) × Mx k r → (Wq →L[ℂ] Wp)),
    IsOpen U ∧ (c₀, g₀) ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ x ∈ U, x.1 ∈ OmX r → x.2 ∈ Glev k r i → x.2 ∈ D → Φ x.1 x.2 = F x

theorem famD_FFl {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    {i : Fin (r + 1)} {D : Set (Mx k r)} (hD : IsOpen D) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : FamD z z' π π' i D Φ)
    {c : Fin r → ℂ} (hc : c ∈ OmX r) : Φ c ∈ FFl k r z z' π π' i D := by
  refine ⟨?_, (hΦ.1 c hc).1, (hΦ.1 c hc).2.1, (hΦ.1 c hc).2.2⟩
  intro g₀ hg₀
  obtain ⟨U, F, hU, hx, hF, hΦF⟩ := hΦ.2 c hc g₀ hg₀
  refine ⟨(fun g => (c, g)) ⁻¹' U ∩ D, fun g => F (c, g), (hU.preimage (by fun_prop)).inter hD, ⟨hx, hg₀.2⟩, ?_,
    fun g hg hgl => hΦF (c, g) hg.1 hc hgl hg.2⟩
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun g hg => hg.1)

theorem upd_mem {c : Fin r → ℂ} (hc : c ∈ OmX r) {c'' : ℂ} (h : c'' ≠ 0) (l : Fin r) :
    Function.update c l c'' ∈ OmX r := by
  intro a
  by_cases ha : a = l
  · subst ha; simpa using h
  · simpa [Function.update_apply, ha] using hc a

def JxF (l : Fin r) (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) : Fn k r (Wq →L[ℂ] Wp) :=
  fun c g => (psi k r z cStd (uL k r l g) * psi k r z' cStd (iH (uL k r l (iH g)))) •
    Φ (Function.update c l (cF k r l g)) (rho k r l g)

theorem dec_JxF {l : Fin r} {g u g₁ u' : Mx k r} {c' : ℂ} (h : Dec k r l g c' u g₁ u')
    (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) :
    JxF l z z' Φ c g = (psi k r z cStd u * psi k r z' cStd u') • Φ (Function.update c l c') g₁ := by
  unfold JxF
  rw [h.uL_eq, h.uL_iH, h.cF_eq, h.rho_eq, iH_eq (up_inv h.hu').1.1, inv_inv' h.hu'.1.1]

theorem descended_function_apply_w1_mul {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r)
    (Φ : Fn k r (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) {c' : ℂ} (hc' : c' ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    JxF l z z' Φ c (w1 k r l c' * g) = Φ (Function.update c l c') g := by
  rw [dec_JxF (dec_w hc' hg), psi_one hz, psi_one hz', one_mul, one_smul]

theorem w1_mul_mem_descended_set_iff (l : Fin r) (D₁ : Set (Mx k r)) {c : ℂ} (hc : c ≠ 0) {g : Mx k r} (hg : g ∈ Glev k r l.succ) :
    w1 k r l c * g ∈ D0 k r l D₁ ↔ g ∈ D₁ := by
  have d := dec_w (l := l) hc hg
  constructor
  · intro h
    have h2 : rho k r l (w1 k r l c * g) ∈ D₁ := h.2
    rwa [d.rho_eq] at h2
  · intro h
    refine ⟨d.cell_decomposition_mem, ?_⟩
    show rho k r l (w1 k r l c * g) ∈ D₁
    rw [d.rho_eq]; exact h

theorem smM_snd (s : Set ((Fin r → ℂ) × Mx k r)) : SmM (fun x : (Fin r → ℂ) × Mx k r => x.2) s := fun i j =>
  ((contDiff_apply_apply ℝ i j).comp contDiff_snd).contDiffOn

theorem descended_set_is_domain {z z' : Fin (2 * r + k + 1) → ℂ} (l : Fin r) {D₁ : Set (Mx k r)} (hD₁ : IsDom k r z z' l.succ D₁) :
    IsDom k r z z' l.castSucc (D0 k r l D₁) := by
  refine ⟨isOpen_cell_domain hD₁.1, ?_⟩
  rintro g hg s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
  obtain ⟨c, u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
  obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hm
  obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hm'
  have d1 := (((((d.leftG hn₁.2).leftU hu₂).leftG (uw_glev hh _)).rightG (uw_glev hh' _)).rightG hn₃.2).rightU hu₃
  have e : h * (u₂ * n₁) * g * (h' * (n₃ * u₃)) = h * (u₂ * (n₁ * g)) * h' * n₃ * u₃ := by
    simp only [Matrix.mul_assoc]
  rw [e]
  refine (mem_cell_domain_iff.2 ⟨_, _, _, _, d1, ?_⟩).2
  have h2 := hD₁.2 g₁ ⟨d.hg, hg₁⟩ (h * n₁) ⟨h, hh, n₁, hn₁, rfl⟩ (h' * n₃) ⟨h', hh', n₃, hn₃, rfl⟩
  have e2 : h * (n₁ * g₁) * h' * n₃ = h * n₁ * g₁ * (h' * n₃) := by simp only [Matrix.mul_assoc]
  rw [e2]; exact h2

theorem famStep {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') (l : Fin r) {D₁ : Set (Mx k r)}
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : FamD z z' π π' l.succ D₁ Φ) :
    FamD z z' π π' l.castSucc (D0 k r l D₁) (JxF l z z' Φ) := by
  refine ⟨fun c hc => ⟨?_, ?_, ?_⟩, ?_⟩
  ·
    intro g hg n hn
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₂, hu₂, n₁, hn₁, rfl⟩ := nlev_dec hn
    have d1 := (d.leftG hn₁.2).leftU hu₂
    have hL := (hΦ.1 _ (upd_mem hc d.hc l)).1 g₁ ⟨d.hg, hg₁⟩ n₁ hn₁
    rw [Matrix.mul_assoc, dec_JxF d1, dec_JxF d, hL,
      psi_mul hz (up_nset hu₂) (up_nset (up_conj d.hu hn₁.2)), psi_conjN hz hn₁.1 (up_nset d.hu),
      psi_mul hz (up_nset hu₂) hn₁.1]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg n hn
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    obtain ⟨u₃, hu₃, n₃, hn₃, rfl⟩ := nlev_dec' hn
    have d1 := (d.rightG hn₃.2).rightU hu₃
    have hR := (hΦ.1 _ (upd_mem hc d.hc l)).2.1 g₁ ⟨d.hg, hg₁⟩ n₃ hn₃
    rw [← Matrix.mul_assoc, dec_JxF d1, dec_JxF d, hR,
      psi_mul hz' (up_nset (up_conj' d.hu' hn₃.2)) (up_nset hu₃), psi_conjN' hz' hn₃.1 (up_nset d.hu'),
      psi_mul hz' hn₃.1 (up_nset hu₃)]
    simp only [smul_smul]
    congr 1
    ring
  ·
    intro g hg h hh h' hh'
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg
    have d1 := (d.leftG (uw_glev hh _)).rightG (uw_glev hh' _)
    have hW := (hΦ.1 _ (upd_mem hc d.hc l)).2.2 g₁ ⟨d.hg, hg₁⟩ h hh h' hh'
    rw [dec_JxF d1, dec_JxF d, hW, psi_conjW hz hh (up_nset d.hu), psi_conjW' hz' hh' (up_nset d.hu')]
    ext v
    simp
  ·
    intro c₀ hc₀ g₀ hg₀
    obtain ⟨c'', u, g₁, u', d, hg₁⟩ := mem_cell_domain_iff.1 hg₀
    obtain ⟨U₁, F₁, hU₁, hmem, hF₁, hag⟩ := hΦ.2 (Function.update c₀ l c'') (upd_mem hc₀ d.hc l) g₁ ⟨d.hg, hg₁⟩
    have hs0 : IsOpen {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := isOpen_adelicUnipotentTimesIntegralOutsideSet.preimage continuous_snd
    have h1 := smM_snd (k := k) (r := r) {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l}
    have hupd : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => Function.update x.1 l (cF k r l x.2))
        {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := by
      refine contDiffOn_pi.2 fun a => ?_
      by_cases ha : a = l
      · subst ha
        exact (sm_cF (l := a) h1).congr fun x _ => by simp
      · exact ((contDiff_apply ℝ (fun _ => ℂ) a).comp contDiff_fst).contDiffOn.congr fun x _ => by
          simp [ha]
    have hrho : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => rho k r l x.2)
        {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} :=
      (smM_contDiffOn smM_rho).comp contDiff_snd.contDiffOn fun x hx => hx
    have hm := hupd.prodMk hrho
    refine ⟨{x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
        (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁,
      fun x => (psi k r z cStd (uL k r l x.2) * psi k r z' cStd (iH (uL k r l (iH x.2)))) •
        F₁ (Function.update x.1 l (cF k r l x.2), rho k r l x.2),
      hm.continuousOn.isOpen_inter_preimage hs0 hU₁, ⟨d.cell_decomposition_mem, ?_⟩, ?_, ?_⟩
    · show (Function.update c₀ l (cF k r l g₀), rho k r l g₀) ∈ U₁
      rw [d.cF_eq, d.rho_eq]; exact hmem
    · have hs : {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
          (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁ ⊆
          {x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} := Set.inter_subset_left
      have h1' := smM_snd (k := k) (r := r) ({x : (Fin r → ℂ) × Mx k r | x.2 ∈ C0 k r l} ∩
          (fun x : (Fin r → ℂ) × Mx k r => (Function.update x.1 l (cF k r l x.2), rho k r l x.2)) ⁻¹' U₁)
      have h2 : SmM (fun x : (Fin r → ℂ) × Mx k r => uL k r l x.2) _ := smM_uL h1' fun x hx => hx.1.1
      have h3 : SmM (fun x : (Fin r → ℂ) × Mx k r => uL k r l (iH x.2)) _ := smM_uL (smM_iH h1') fun x hx => hx.1.2
      have h5 := hF₁.comp (hm.mono hs) fun x hx => hx.2
      exact ((sm_psi z cStd h2).mul (sm_psi z' cStd (smM_iH h3))).smul h5
    · intro x hxU hx1 hxG hxD
      obtain ⟨u3, g3, u3', d3⟩ := dec_exists hxG hxU.1.1
      have hy := hag (Function.update x.1 l (cF k r l x.2), rho k r l x.2) hxU.2 (upd_mem hx1 hxU.1.1 l)
        (by show rho k r l x.2 ∈ Glev k r l.succ; rw [d3.rho_eq]; exact d3.hg) hxD.2
      show JxF l z z' Φ x.1 x.2 = _
      unfold JxF
      rw [hy]

end fam

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc
end
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

open Formalism.FourierDecayAlt.P.Qx4

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section iter

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
  {k r : ℕ}

def lev (r i : ℕ) : Fin (r + 1) := ⟨min i r, by omega⟩

theorem lev_castSucc (i : ℕ) (h : i < r) : (⟨i, h⟩ : Fin r).castSucc = lev r i := Fin.ext (by simp [lev]; omega)
theorem lev_succ (i : ℕ) (h : i < r) : (⟨i, h⟩ : Fin r).succ = lev r (i + 1) := Fin.ext (by simp [lev]; omega)
theorem lev_r : lev r r = Fin.last r := Fin.ext (by simp [lev])
theorem lev_zero : lev r 0 = 0 := Fin.ext (by simp [lev])

def Dn (z z' : Fin (2 * r + k + 1) → ℂ) (i : ℕ) : Set (Mx k r) :=
  if h : i < r then D0 k r ⟨i, h⟩ (Dn z z' (i + 1)) else Qx8.Dp k r z z'
termination_by r - i

def Kn (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) (i : ℕ) : Fn k r (Wq →L[ℂ] Wp) :=
  if h : i < r then JxF ⟨i, h⟩ z z' (Kn z z' Φ (i + 1)) else Φ
termination_by r - i

theorem Dn_lt (z z' : Fin (2 * r + k + 1) → ℂ) {i : ℕ} (h : i < r) :
    Dn z z' i = D0 k r ⟨i, h⟩ (Dn z z' (i + 1)) := by
  rw [Dn, dite_eq_left h]

theorem Dn_ge (z z' : Fin (2 * r + k + 1) → ℂ) {i : ℕ} (h : ¬ i < r) : Dn z z' i = Qx8.Dp k r z z' := by
  rw [Dn, dite_eq_right h]

theorem Kn_lt (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) {i : ℕ} (h : i < r) :
    Kn z z' Φ i = JxF ⟨i, h⟩ z z' (Kn z z' Φ (i + 1)) := by
  rw [Kn, dite_eq_left h]

theorem Kn_ge (z z' : Fin (2 * r + k + 1) → ℂ) (Φ : Fn k r (Wq →L[ℂ] Wp)) {i : ℕ} (h : ¬ i < r) :
    Kn z z' Φ i = Φ := by
  rw [Kn, dite_eq_right h]

theorem famR {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    FamD z z' π π' (Fin.last r) (Qx8.Dp k r z z') Φ := by
  refine ⟨fun c hc => ?_, fun c₀ hc₀ g₀ hg₀ => ?_⟩
  · have h := Qx8.slice_FF hz hz' hΦ hc
    exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  · obtain ⟨U, F, hU, hx, hF, hΦF⟩ := hΦ.2.1 (c₀, g₀) ⟨hc₀, hg₀.1, hg₀.2⟩
    exact ⟨U, F, hU, hx, hF, fun x hx _ hg _ => hΦF x hx hg⟩

theorem allLev {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
    (hz : inWb k r z) (hz' : inWb k r z') {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    ∀ j, j ≤ r → IsDom k r z z' (lev r (r - j)) (Dn z z' (r - j)) ∧
      FamD z z' π π' (lev r (r - j)) (Dn z z' (r - j)) (Kn z z' Φ (r - j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [Nat.sub_zero]
    rw [lev_r, Dn_ge z z' (lt_irrefl r), Kn_ge z z' Φ (lt_irrefl r)]
    exact ⟨Qx8.Dp_dom k r z z', famR hz hz' hΦ⟩
  | succ j ih =>
    intro hj
    obtain ⟨hD, hF⟩ := ih (by omega)
    have hi : r - (j + 1) < r := by omega
    have e : r - j = r - (j + 1) + 1 := by omega
    rw [e, ← lev_succ _ hi] at hD hF
    rw [← lev_castSucc _ hi, Dn_lt z z' hi, Kn_lt z z' Φ hi]
    exact ⟨descended_set_is_domain _ hD, famStep hz hz' _ hF⟩

def mix (i : ℕ) (c d : Fin r → ℂ) : Fin r → ℂ := fun a => if a.val < i then c a else d a

theorem vals {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (Φ : Fn k r (Wq →L[ℂ] Wp))
    (d : Fin r → ℂ) {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    ∀ i, i ≤ r → ∀ X ∈ Glev k r (lev r i) ∩ Dn z z' i,
      wCell k r (lev r i) c * X ∈ Glev k r 0 ∩ Dn z z' 0 ∧
        Kn z z' Φ 0 d (wCell k r (lev r i) c * X) = Kn z z' Φ i (mix i c d) X := by
  intro i
  induction i with
  | zero =>
    intro _ X hX
    have hm : mix 0 c d = d := funext fun a => by simp [mix]
    rw [lev_zero] at hX ⊢
    rw [Qx6.wCell_zero, Matrix.one_mul, hm]
    exact ⟨hX, rfl⟩
  | succ i ih =>
    intro hi X hX
    have hlt : i < r := by omega
    obtain ⟨l, hl⟩ : ∃ l : Fin r, l = ⟨i, hlt⟩ := ⟨_, rfl⟩
    have hli : l.val = i := by rw [hl]
    have hcs : l.castSucc = lev r i := by rw [hl]; exact lev_castSucc i hlt
    have hsc : l.succ = lev r (i + 1) := by rw [hl]; exact lev_succ i hlt
    have hDi : Dn z z' i = D0 k r l (Dn z z' (i + 1)) := by rw [hl]; exact Dn_lt z z' hlt
    have hKi : Kn z z' Φ i = JxF l z z' (Kn z z' Φ (i + 1)) := by rw [hl]; exact Kn_lt z z' Φ hlt
    rw [← hsc] at hX ⊢
    have hcl : c l ≠ 0 := hc l
    have hX' : w1 k r l (c l) * X ∈ Glev k r (lev r i) ∩ Dn z z' i := by
      rw [← hcs, hDi]
      exact ⟨glev_mul (weyl_cell_mem_level_group (l := l) hcl) (glev_succ_le hX.1), (w1_mul_mem_descended_set_iff l _ hcl hX.1).2 hX.2⟩
    obtain ⟨hmem, hval⟩ := ih (by omega) _ hX'
    have hmix : Function.update (mix i c d) l (c l) = mix (i + 1) c d := by
      funext a
      by_cases ha : a = l
      · subst ha; simp [mix, hli]
      · have hne : a.val ≠ i := fun h => ha (Fin.ext (by rw [h, hli]))
        simp only [mix, Function.update_apply, ha, if_false]
        by_cases h1 : a.val < i
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    rw [Qx6.wCell_succ, Matrix.mul_assoc, hcs]
    refine ⟨hmem, ?_⟩
    rw [hval, hKi, descended_function_apply_w1_mul hz hz' l _ _ hcl hX.1, hmix]

end iter

end Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.CutMP.JA.SA.Desc

theorem self_adjoint_descent_holds : SADescend := by
  intro Wp Wq _ _ _ _ k r z z' π π' hz hz' Φ hΦ
  have hall := allLev (π := π) (π' := π') hz hz' hΦ r le_rfl
  rw [Nat.sub_self, lev_zero] at hall
  obtain ⟨hD, hF⟩ := hall
  refine ⟨Dn z z' 0, hD, Kn z z' Φ 0 (fun _ => 1), famD_FFl hD.1 hF (fun _ => one_ne_zero), ?_⟩
  intro c hc g hg hGG
  have hv := vals hz hz' Φ (fun _ => 1) hc r le_rfl g
    ⟨by rw [lev_r]; exact hg, by rw [Dn_ge z z' (lt_irrefl r)]; exact hGG⟩
  rw [lev_r] at hv
  have hm : mix r c (fun _ => 1) = c := funext fun a => by simp [mix, a.isLt]
  rw [hm, Kn_ge z z' Φ (lt_irrefl r)] at hv
  exact ⟨hv.1.2, hv.2⟩

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecCover
open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem self_adjoint_cover_holds : SACover := by
  intro k r z z' hz hz' g hg
  obtain ⟨hg0, hD, hG⟩ := hg
  obtain ⟨n, hn, n', hn', c, hc, μ, hμ, hgeq⟩ := Formalism.FourierDecayAlt.P.big_cell_decomposition k r z z' g hg0.1 hD
  have e : bigCell k r c μ = wCell k r (Fin.last r) c * B2.embWb k r μ := by
    rw [Formalism.FourierDecayAlt.P5.Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  have hg1 : B2.embWb k r μ ∈ Glev k r (Fin.last r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mem_UWb hμ)
  have hninv : n⁻¹ ∈ Nset k r := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn

  have hDinv : ∀ l, Dmin k r z z' g l = Dmin k r z z' (bigCell k r c μ) l := by
    intro l
    rw [hgeq]
    exact dInv k r z z' hz hz' _ (Formalism.FourierDecayAlt.P.BigCellDecomposition.n_inv_S hn) _ (Formalism.FourierDecayAlt.P.BigCellDecomposition.n_S hn') _ l
  have hGb : 0 < Gf k r z z' (bigCell k r c μ) := by
    have e2 : Gf k r z z' g = Gf k r z z' (bigCell k r c μ) := by
      unfold Gf; rw [hDinv, hDinv]
    rw [← e2]; exact hG
  have hGG : 0 < GGl k r z z' (B2.embWb k r μ) := by
    have hmin := big_cell_minors_holds k r z z' c μ hz hz'
    have hζ : herm (Hpk k r) (bigCell k r c μ *ᵥ z') z = zetaL k r z z' (Fin.last r) (B2.embWb k r μ) := by
      rw [Formalism.FourierDecayAlt.P5.Rad.zetaL_last, ← Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hz', Formalism.FourierDecayAlt.P.BigCellHermitian.bigCell_mulVec_jV,
        Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV]
    have hzeta := hmin.2.2 hc
    rw [hζ] at hzeta
    have hr := hmin.1 (Fin.last r)
    set Pd := Dmin k r z z' (bigCell k r c μ) ⟨r, by omega⟩ with hPd
    have hP0 : Pd ≠ 0 := by
      have : Pd = ∏ a : Fin r with a.val < (Fin.last r).val, c a := hr
      rw [this]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
    have hlast : Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1)) =
        zetaL k r z z' (Fin.last r) (B2.embWb k r μ) * Pd := by
      unfold Formalism.QuantumDeterminants.zeta at hzeta
      rw [← hPd] at hzeta
      have h2 := div_mul_cancel₀ (Dmin k r z z' (bigCell k r c μ) (Fin.last (r + 1))) hP0
      rw [hzeta] at h2
      exact h2.symm
    have hGb' := hGb
    unfold Gf at hGb'
    rw [hlast, ← hPd, Complex.normSq_mul] at hGb'
    have h1 : 0 < Complex.normSq Pd := Complex.normSq_pos.2 hP0
    unfold GGl
    nlinarith
  refine ⟨n⁻¹, ⟨hninv, hninv.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, n', ⟨hn', hn'.1, fun a ha => absurd ha (Nat.not_lt_zero _)⟩,
    c, hc, B2.embWb k r μ, hg1, hGG, ?_⟩
  rw [hgeq, e]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecAsm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

theorem sec_at (hR : SARadSec) (hD : SADescend) (hC : SACover)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : Gauge.IsFrameB P Bs e)
    (U : M.Ty P → MA.SmQ P.r P.TT) :
    ∃ K ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Q.OmPlus P.k P.r Bs.z Bs.z'), Gauge.trJB P Bs e K = U := by
  obtain ⟨Φ, hΦ, hval⟩ := hR Wp Wq P Bs hpl e he U
  obtain ⟨D₀, hD₀, K, hK, hKv⟩ := hD Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' Bs.z_mem Bs.z'_mem Φ hΦ
  have hsub : ∀ g ∈ Q.Glev P.k P.r 0 ∩ Q.OmPlus P.k P.r Bs.z Bs.z', g ∈ D₀ := by
    intro g hg
    obtain ⟨n, hn, n', hn', c, hc, g₁, hg₁, hGG, hgeq⟩ := hC P.k P.r Bs.z Bs.z' Bs.z_mem Bs.z'_mem g hg
    have hw := (hKv c hc g₁ hg₁ hGG).1
    have hwG : Q.wCell P.k P.r (Fin.last P.r) c * g₁ ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg₁)
    rw [hgeq]
    exact hD₀.2 _ ⟨hwG, hw⟩ n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n, hn, (Matrix.one_mul n).symm⟩ n'
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n', hn', (Matrix.one_mul n').symm⟩
  refine ⟨K, ?_, ?_⟩
  · obtain ⟨hs, hL, hRt, hW⟩ := hK
    exact ⟨fun g₀ hg₀ => hs g₀ ⟨hg₀.1, hsub g₀ hg₀⟩, fun g hg n hn => hL g ⟨hg.1, hsub g hg⟩ n hn,
      fun g hg n hn => hRt g ⟨hg.1, hsub g hg⟩ n hn, fun g hg h hh h' hh' => hW g ⟨hg.1, hsub g hg⟩ h hh h' hh'⟩
  · funext ρ
    have hraw : Gauge.rawJ P Bs e K ρ = (U ρ : MA.Qp P.r P.TT → ℂ) := by
      funext q
      have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
        rw [Gauge.GC.SSTr.tz_eq P Bs hpl]; exact q.2.2
      have hG : NF.muZ P.k P.r Bs.μsec q.1.2 ∈ Q.Glev P.k P.r (Fin.last P.r) :=
        Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb Bs.sec hζ)
      have hGG : 0 < Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) := by
        unfold Q.GGl
        rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ Bs.z_mem Bs.z'_mem Bs.sec hζ]
        linarith
      have hζ' : P.TT < Complex.normSq q.1.2 := q.2.2
      have horth := (he.2 q.1.2 hζ').2.1
      have hwpos : 0 < Real.sqrt (MA.wq P.k q.1 P.TT) := Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos q.2)
      have hw : ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hwpos.ne'
      simp only [Gauge.rawJ]
      rw [Gauge.tc_gq, (hKv q.1.1 q.2.1 _ hG hGG).2, hval q, Gauge.tc_hsVec_smul, inner_smul_right,
        Gauge.tc_hsVec_sum, inner_sum]
      simp only [Gauge.tc_hsVec_smul, inner_smul_right, horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      push_cast
      field_simp
    show MA.toSm P (Gauge.rawJ P Bs e K ρ) = U ρ
    have hm : Gauge.rawJ P Bs e K ρ ∈ MA.smSub P.r P.TT := by rw [hraw]; exact (U ρ).2
    rw [Gauge.toSm_of_mem P hm]
    apply Subtype.ext
    exact hraw

theorem sASection_of_parts (hR : SARadSec) (hD : SADescend) (hC : SACover) : SASection := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he U _
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  obtain ⟨K, hK, hKU⟩ := sec_at hR hD hC (D.parOf S v) (T v).base hpl e he U
  refine ⟨K, ?_, hKU⟩
  show K ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v)
  rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.omP_eq E Wp Wq S T v]
  exact hK

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecRad
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_section_holds : SARadSec := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl e he U
  classical
  let g : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := fun x =>
    (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) • ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2
  let φ := (NF.QR P.k P.r Bs.z Bs.z').indicator g
  have hQR : NF.QR P.k P.r Bs.z Bs.z' = MA.Qset P.r P.TT := Set.ext (qr_iff P Bs hpl)
  have hg : ContDiffOn ℝ ∞ g (MA.Qset P.r P.TT) := by
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E P.r => (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ))
        (MA.Qset P.r P.TT) := by
      refine Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_ofReal ?_
      refine ContDiffOn.inv ?_ fun x hx => (Real.sqrt_pos.2 (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx)).ne'
      exact (Formalism.FourierDecayAlt.P.CutMP.En.wq_contDiff P.k P.r P.TT).contDiffOn.sqrt fun x hx =>
        (Formalism.FourierDecayAlt.P.CutMP.En.wq_pos hx).ne'
    refine hw.smul (ContDiffOn.sum fun ρ _ => ?_)
    have hF : ContDiffOn ℝ ∞ (MA.ext (U ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) := (U ρ).2
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E P.r => e ρ x.2) (MA.Qset P.r P.TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    exact hF.smul he'
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
    · rw [hQR]
      exact hg.congr fun x hx => by simp only [φ, hQR, Set.indicator_of_mem hx]
    · simp only [φ, Set.indicator_of_mem hx, g]
      have hx' : P.TT < Complex.normSq x.2 := ((qr_iff P Bs hpl x).1 hx).2
      have h1 := fib_sum_smul P Bs x.2 (fun ρ => MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x) (fun ρ => e ρ x.2) fun ρ => (he.2 x.2 hx').1 ρ
      by_cases hne : Nonempty (M.Ty P)
      · obtain ⟨ρ0⟩ := hne
        intro p hp
        have h3 := fib_sum_smul P Bs x.2 (fun ρ => if ρ = ρ0 then (((Real.sqrt (MA.wq P.k x P.TT))⁻¹ : ℝ) : ℂ) else 0)
          (fun _ => ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2) (fun _ => h1) p hp
        simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h3
        exact h3
      · have : ∑ ρ, MA.ext (U ρ : MA.Qp P.r P.TT → ℂ) x • e ρ x.2 = 0 := by
          rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hne)]; simp
        rw [this, smul_zero]
        intro p hp
        ext v
        simp
    · simp [φ, Set.indicator_of_notMem hx]
  obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π'
    (radBase P Bs hpl) φ hφ
  refine ⟨Φ, hΦ, fun q => ?_⟩
  have hq : q.1 ∈ NF.QR P.k P.r Bs.z Bs.z' := (qr_iff P Bs hpl q.1).2 q.2
  have h := congrFun hrad q.1
  simp only [NF.radR, Set.indicator_of_mem hq, φ] at h
  rw [h]
  simp only [g]
  congr 1
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  simp [MA.ext, q.2]

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem self_adjoint_section_holds : Formalism.FourierDecayAlt.P.CutMP.JA.SA.SASection :=
  Formalism.FourierDecayAlt.P.CutMP.JA.SA.sASection_of_parts Formalism.FourierDecayAlt.P.CutMP.JA.SA.radial_section_holds
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_descent_holds Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_cover_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
