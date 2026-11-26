module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorFinal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacLineTransp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


omit [NumberField F] [NumberField E] in
theorem symp_transpose {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K] (c : K →ₐ[R] K)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : K) (JA : Matrix α α K) (JB : Matrix β β K)
    (x y : Matrix α β K) : symp (R := R) c ξ JB JA xᵀ yᵀ = symp (R := R) c ξ JA JB x y := by
  unfold symp hTens
  congr 2
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [NumberField E] in
theorem at_transpose {m n : Type} (v : Pl (F := F)) (z : Matrix m n (AE F E)) :
    At (evFin F v) zᵀ ↔ At (evFin F v) z := by
  constructor
  · intro h u hu
    have := h u hu
    rw [← Matrix.transpose_smul] at this
    simpa using congrArg Matrix.transpose this
  · intro h u hu
    rw [← Matrix.transpose_smul, h u hu, Matrix.transpose_zero]

theorem transpose_mem_latAtV {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) {z : Matrix (Fin n) (Fin d) (AE F E)}
    (hz : z ∈ latAtV X Y v) : zᵀ ∈ latAtV Y X v := by
  have hle : latAtV X Y v ≤ (latAtV Y X v).comap (Matrix.transposeAddEquiv (Fin n) (Fin d) (AE F E)).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).mpr ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, y, hy, x, hx, ?_⟩
    show (a • incM F (Matrix.vecMulVec x y))ᵀ = _
    simp only [incM, Matrix.transpose_smul, ← Matrix.transpose_map, Matrix.transpose_vecMulVec]
  exact hle hz

theorem mem_latAtV_transpose {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl (F := F)) (z : Matrix (Fin n) (Fin d) (AE F E)) :
    zᵀ ∈ latAtV Y X v ↔ z ∈ latAtV X Y v :=
  ⟨fun h => by simpa using transpose_mem_latAtV Y X v h, transpose_mem_latAtV X Y v⟩


open GlobalTheory.DblVacLine in
theorem dbl_line_co {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    (v : Pl (F := F)) (hunr : PsiUnr ψ v) (hX : X.L.IsLattice E) (hY : Y.L.IsLattice E)
    (hsd : ∀ z : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) z → (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
      ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J) z γ) = 1))
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F Y.J)) κ) (φ : (κ → Fv F v) → ℂ)
    (hφ : φ ∈ SB _ ∧ φ ≠ 0 ∧ ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 ∧ ∀ γ ∈ latAtV X Y v, Acts (evFin F v) (co.rho ψ γ) φ
      (ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F Y.J) γ γ) • φ))
    (dd : Darboux (symp (cA σ) (-1) (incM F X.J) (dbl (incM F Y.J))) (κ ⊕ κ))
    (omd : UG (cA σ) (dbl (incM F Y.J)) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (hdd : IsDblCoord (cA σ) (-1) (incM F X.J) (incM F Y.J) co dd)
    (hS : IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd)
    (R : (κ → AF F) → ℂ) (hR : Rest (evFin F v) φ R)
    (g : GlobalTheory.InertDbl.UD σ Y) (hg : g ∈ GlobalTheory.InertDbl.KAtD σ Y v) :
    ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R)) = c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R) := by
  classical
  by_cases hR0 : R = 0
  · have e : GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R) = 0 := by
      funext x; simp [hR0, GlobalTheory.InertDbl.dblFun, boxFun, tens]
    exact ⟨0, by rw [e, map_zero, smul_zero]⟩
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hR0
  obtain ⟨hφSB, hφ0, θ, -, hvac⟩ := hφ
  have hn := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  set Λ := latAtV X Y v with hΛ
  have hat : ∀ γ ∈ Λ, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X Y v).1
  set φd := boxFun φ fun x => star (φ x) with hφd
  set Rd := GlobalTheory.InertDbl.dblFun R with hRd
  set Φ := GlobalTheory.InertDbl.dblFun (tens (evFin F v) φ R) with hΦ
  have hΦt : Φ = tens (evFin F v) φd Rd := dblFun_tens v φ R
  have hrest : Rest (evFin F v) φd Rd := rest_dbl v hR
  have hΦs : Φ ∈ schA F _ := hΦt ▸ hrest.2
  have hRd0 : Rd (Sum.elim x₀ x₀) ≠ 0 := by
    show R x₀ * star (R x₀) ≠ 0
    exact mul_ne_zero hx₀ (star_ne_zero.mpr hx₀)
  have hφdSB : φd ∈ SB _ := box_mem_SB hφSB ⟨hφSB.1.comp star, hφSB.2.comp_left (star_zero ℂ)⟩
  let cf : Matrix (Fin n) (Fin d ⊕ Fin d) (AE F E) → ℂ := fun w =>
    ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (dbl (incM F Y.J)) w w)

  have h1 : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ, dd.rho ψ (Matrix.fromCols γ₁ γ₂) Φ = cf (Matrix.fromCols γ₁ γ₂) • Φ := by
    intro γ₁ h₁ γ₂ h₂
    have e₁ := hvac γ₁ h₁ R hR
    have e₂ := hvac γ₂ h₂ R hR
    rw [GlobalTheory.VacTransport.tens_smul] at e₁ e₂
    simp only [Darboux.rho] at e₁ e₂
    rw [Darboux.rho, hdd, hΦ, GlobalTheory.InertDbl.dblFun, schr_box ψ hn, e₁, e₂]
    funext x
    simp only [cf, symp_dbl, boxFun, Pi.smul_apply, smul_eq_mul, star_mul', star_eq_neg ψ hn, mul_sub]
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring

  have h2 : ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ,
      dd.rho ψ (Matrix.fromCols γ₁ γ₂) (omd g Φ) = cf (Matrix.fromCols γ₁ γ₂) • omd g Φ := by
    intro γ₁ h₁ γ₂ h₂
    obtain ⟨δ₁, k₁, δ₂, k₂, he⟩ := fromCols_mul_transpose X Y v (GlobalTheory.InertDbl.matD g⁻¹) (fun z hz => (hg.2 z hz).2) h₁ h₂
    have hback : actB (cA σ) g (Matrix.fromCols δ₁ δ₂) = Matrix.fromCols γ₁ γ₂ := by
      change Matrix.fromCols δ₁ δ₂ * (GlobalTheory.InertDbl.matD g)ᵀ = _
      have e : GlobalTheory.InertDbl.matD g * GlobalTheory.InertDbl.matD g⁻¹ = 1 := Units.mul_inv g.1
      rw [← he, Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
    have hsy : cf (Matrix.fromCols δ₁ δ₂) = cf (Matrix.fromCols γ₁ γ₂) := by
      simp only [cf]
      rw [← he, GlobalTheory.VacTransport.symp_mul_transpose (cA σ) _ _ _ (GlobalTheory.InertDbl.matD g⁻¹) (g⁻¹).2]
    have h := hS.impl g (Matrix.fromCols δ₁ δ₂) Φ hΦs
    rw [hback, h1 δ₁ k₁ δ₂ k₂, map_smul, hsy] at h
    exact h.symm

  obtain ⟨φ₁, -, hact⟩ := acts_of_at hψ dd omd hS v g hg.1 φd hφdSB
  have hT : omd g Φ = tens (evFin F v) φ₁ Rd := by rw [hΦt]; exact hact Rd hrest
  have hrest₁ : Rest (evFin F v) φ₁ Rd := ⟨hrest.1, hT ▸ hS.pres g Φ hΦs⟩
  have hloc : ∀ f, Rest (evFin F v) f Rd → ∀ γ₁ ∈ Λ, ∀ γ₂ ∈ Λ,
      dd.rho ψ (Matrix.fromCols γ₁ γ₂) (tens (evFin F v) f Rd) = cf (Matrix.fromCols γ₁ γ₂) • tens (evFin F v) f Rd →
      schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂)) f = cf (Matrix.fromCols γ₁ γ₂) • f := by
    intro f hf γ₁ h₁ γ₂ h₂ h
    refine eq_of_tens v hf.1 hRd0 ?_
    rw [GlobalTheory.VacTransport.tens_smul, ← h]
    exact (GlobalTheory.VacBridge.rho_acts_locCo dd ψ v _ (at_fromCols v (hat _ h₁) (hat _ h₂)) f Rd hf).symm
  have hco : ∀ γ₁ γ₂, GlobalTheory.LatVac.locCo dd v (Matrix.fromCols γ₁ γ₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo co v γ₁).1 (GlobalTheory.LatVac.locCo co v γ₂).1,
        Sum.elim (GlobalTheory.LatVac.locCo co v γ₁).2 (-(GlobalTheory.LatVac.locCo co v γ₂).2)) := by
    intro γ₁ γ₂
    change ((fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).1 k)),
      fun k => evFin F v ((dd.e (Matrix.fromCols γ₁ γ₂)).2 k)) = _
    rw [hdd]
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · cases k <;> rfl
    · cases k with
      | inl k => rfl
      | inr k => exact map_neg (evFin F v) _

  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X Y v co hX hY
  have hfill := GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator v (GlobalTheory.LatVac.psiAt ψ v)
    (Λ.map (GlobalTheory.LatVac.locCo co v)) c hc0 (fun x => hunr x) (GlobalTheory.LatVac.DualLoc.map_selfDual v co ψ Λ hat hsd)
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  have hφd0 : φd ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hφ0
    refine Function.ne_iff.mpr ⟨Sum.elim t t, ?_⟩
    show φ t * star (φ t) ≠ 0
    exact mul_ne_zero ht (star_ne_zero.mpr ht)
  obtain ⟨c', hc'⟩ := GlobalTheory.VacUniqInert.eq_smul_of_eigen (GlobalTheory.LatVac.psiAt ψ v)
    (fun i : Λ × Λ => GlobalTheory.LatVac.locCo dd v (Matrix.fromCols i.1.1 i.2.1))
    (fun i => cf (Matrix.fromCols i.1.1 i.2.1)) (fun u hu => by
      have eu : u = Sum.elim (u ∘ Sum.inl) (u ∘ Sum.inr) := (Sum.elim_comp_inl_inr u).symm
      obtain ⟨y₁, γ₁, h₁, e₁⟩ := hfill (u ∘ Sum.inl) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (⟨γ, hγ⟩, 0) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero]
          funext k; cases k <;> rfl)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      obtain ⟨y₂, γ₂, h₂, e₂⟩ := hfill (u ∘ Sum.inr) (by
        rintro b ⟨γ, hγ, he⟩
        have := hu (0, ⟨-γ, neg_mem hγ⟩) (by
          simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg]
          funext k; cases k <;> simp)
        simp only [hco, he, ZeroMemClass.coe_zero, map_zero, map_neg] at this
        rw [eu, sumElim_dotProduct_sumElim] at this
        simpa using this)
      refine ⟨(⟨γ₁, h₁⟩, ⟨γ₂, h₂⟩), ?_⟩
      simp only [hco, e₁, e₂]
      exact eu.symm) φ₁ φd
    (fun i => hloc φ₁ hrest₁ _ i.1.2 _ i.2.2 (hT ▸ h2 _ i.1.2 _ i.2.2))
    (fun i => hloc φd hrest _ i.1.2 _ i.2.2 (hΦt ▸ h1 _ i.1.2 _ i.2.2)) hφd0
  exact ⟨c', by rw [hT, hc', GlobalTheory.VacTransport.tens_smul, ← hΦt]⟩

end GlobalTheory.DblVacLineTransp

namespace GlobalTheory.DblVacLineSplitTransp

open GlobalTheory.DblVacLineTransp

end GlobalTheory.DblVacLineSplitTransp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiVertexLatticeSplitsAlongWittAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiVertexLatticeSplitsAlongWittAtPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.MonoJac

variable {D : D7}

open GlobalTheory.SeeSaw.SplitLat (colProj colProj_mulVec colMul_rat rat_mulVec_mem_latV mulVec_eq_sum_colMul)

theorem monoAt_of_proj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀)
    (hX : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qX d.e i *ᵥ x ∈ L)
    (hY : ∀ i : Fin ρ, ∀ x ∈ L, colProj d.qY d.e' i *ᵥ x ∈ L)
    (h0 : ∀ x ∈ L, d.q0 *ᵥ x ∈ L₀) (hi : ∀ x ∈ L₀, d.i₀ *ᵥ x ∈ L) (v : GlobalTheory.FinPl.Pl D) :
    MonoAt d L L₀ v := by
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · change GlobalTheory.FinPl.colMul (rat d.e) i ((rat d.qX *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hX i) _ hy
    · change GlobalTheory.FinPl.colMul (rat d.e') i ((rat d.qY *ᵥ y) i) ∈ _
      rw [colMul_rat]
      exact rat_mulVec_mem_latV _ (hY i) _ hy
    · exact rat_mulVec_mem_latV d.q0 h0 _ hy
  · rintro ⟨h1, h3, h2⟩
    have hrat : d.e * d.qX + d.i₀ * d.q0 + d.e' * d.qY = 1 := by
      have h : fromRows (fromRows d.qX d.q0) d.qY * fromCols (fromCols d.e d.i₀) d.e' = 1 := by
        rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols,
          GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_i₀,
          GlobalTheory.SeeSaw.SplitLat.qX_e', GlobalTheory.SeeSaw.SplitLat.qY_e,
          GlobalTheory.SeeSaw.SplitLat.qY_i₀, GlobalTheory.SeeSaw.SplitLat.qY_e',
          GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero,
          GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one,
          GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero,
          fromBlocks_one, fromRows_zero, fromCols_zero, fromBlocks_one]
      rw [← fromCols_mul_fromRows, ← fromCols_mul_fromRows]
      exact (Matrix.mul_eq_one_comm_of_card_eq _ _ _ (by simp [← d.rank_add]; ring)).1 h
    have hsum : d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY = 1 := by
      have h := congrArg rat hrat
      change (d.e * d.qX + d.i₀ * d.q0 + d.e' * d.qY).map (incA D) = (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E).map (incA D) at h
      rw [Matrix.map_add _ (map_add (incA D)), Matrix.map_add _ (map_add (incA D)),
        Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_one] at h
      · exact h
      · exact map_zero (incA D)
      · exact map_one (incA D)
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.add_mulVec,
        hsum, Matrix.one_mulVec]
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (sum_mem fun i _ => h1 i) ?_) (sum_mem fun i _ => h3 i)
    exact rat_mulVec_mem_latV d.i₀ hi _ h2

open GlobalTheory.SeeSaw.SplitLat (colProj)

theorem sumLat_map {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (N : Matrix (Fin n) (Fin n) D.host.E) (w : Fin c → D.host.E) (hM : N * M = 0) (ha : N * a = a * Matrix.diagonal w)
    (hw : ∀ p, w p = 0 ∨ w p = 1) : ∀ x ∈ sumLat M Λ a 𝔟, N *ᵥ x ∈ sumLat M Λ a 𝔟 := by
  rintro _ ⟨y, -, u, hu, rfl⟩
  refine ⟨0, Λ.zero_mem, Matrix.diagonal w *ᵥ u, fun p => ?_, ?_⟩
  · rw [Matrix.mulVec_diagonal]
    rcases hw p with h | h
    · rw [h, zero_mul]; exact (𝔟 p).zero_mem
    · rw [h, one_mul]; exact hu p
  · rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, ha, ← Matrix.mulVec_mulVec,
      Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add]

theorem sumLat_proj {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E}
    (q : Matrix (Fin k) (Fin n) D.host.E) (hM : q * M = 1) (ha : q * a = 0) : ∀ x ∈ sumLat M Λ a 𝔟, q *ᵥ x ∈ Λ := by
  rintro _ ⟨y, hy, u, -, rfl⟩
  rwa [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, ha, Matrix.one_mulVec, Matrix.zero_mulVec,
    add_zero]

theorem mem_sumLat_of {n k c : ℕ} {M : Matrix (Fin n) (Fin k) D.host.E} {Λ : Submodule (𝓞 D.host.E) (Fin k → D.host.E)}
    {a : Matrix (Fin n) (Fin c) D.host.E} {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {y : Fin k → D.host.E}
    (hy : y ∈ Λ) : M *ᵥ y ∈ sumLat M Λ a 𝔟 :=
  ⟨y, hy, 0, fun p => (𝔟 p).zero_mem, by rw [Matrix.mulVec_zero, add_zero]⟩

theorem colProj_mul {S : HSp D} {ρ m l : ℕ} (q : Matrix (Fin ρ) (Fin m) D.host.E) (f : Matrix (Fin S.rank) (Fin ρ) D.host.E)
    (i : Fin ρ) (N : Matrix (Fin m) (Fin l) D.host.E) : colProj (S := S) q f i * N = colProj (S := S) (q * N) f i := by
  ext k j
  simp only [colProj, Matrix.mul_apply, Matrix.of_apply, Finset.mul_sum, mul_assoc]

theorem colProj_zero {S : HSp D} {ρ m : ℕ} (f : Matrix (Fin S.rank) (Fin ρ) D.host.E) (i : Fin ρ) :
    colProj (S := S) (0 : Matrix (Fin ρ) (Fin m) D.host.E) f i = 0 := by
  ext k j
  simp [colProj]

section SlopeTestRemainingChoices

variable {A B : HSp D} {c ρ : ℕ}

def cfE (c : ℕ) : Matrix (Fin ρ) (Fin c) D.host.E := fun p q => if p.1 = q.1 then ((-D.host.xi0) ^ (p.1 + 1))⁻¹ else 0

def cfE' (c : ℕ) (s : Fin ρ → D.host.E) : Matrix (Fin ρ) (Fin c) D.host.E := fun p q => if q.1 + p.1 + 1 = c then (s p)⁻¹ else 0

theorem eq_idempotent_mul_add_of_mul_sub_eq {n : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (hc : c = 2 * ρ) (h : ρ ≤ c) (s : Fin ρ → D.host.E)
    (hs : ∀ p, s p ≠ 0) :
    a = (colsOf a (Fin.castLE h) (fun p : Fin ρ => (-D.host.xi0) ^ (p.1 + 1)) : Matrix (Fin n) (Fin ρ) D.host.E) *
        (cfE c : Matrix (Fin ρ) (Fin c) D.host.E) +
      (colsOf a (fun p : Fin ρ => (Fin.castLE h p : Fin c).rev) s : Matrix (Fin n) (Fin ρ) D.host.E) *
        (cfE' c s : Matrix (Fin ρ) (Fin c) D.host.E) := by
  have hx : ∀ p : ℕ, ((-D.host.xi0) ^ (p + 1)) ≠ 0 := fun p => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  refine Matrix.ext fun k q => ?_
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [colsOf, cfE, cfE']
  by_cases hq : q.1 < ρ
  · rw [Finset.sum_eq_single ⟨q.1, hq⟩, Finset.sum_eq_zero]
    · rw [if_pos rfl, add_zero, show (Fin.castLE h ⟨q.1, hq⟩ : Fin c) = q from Fin.ext rfl, mul_comm,
        ← mul_assoc, inv_mul_cancel₀ (hx _), one_mul]
    · intro p _
      rw [if_neg (by omega), mul_zero]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext e)), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · have hp' : c - 1 - q.1 < ρ := by have := q.2; omega
    rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨c - 1 - q.1, hp'⟩]
    · rw [if_pos (by have := q.2; simp only [Fin.val_mk]; omega), zero_add,
        show ((Fin.castLE h ⟨c - 1 - q.1, hp'⟩ : Fin c).rev) = q from Fin.ext (by simp [Fin.val_rev]; omega),
        mul_comm, ← mul_assoc, inv_mul_cancel₀ (hs _), one_mul]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext (show p.1 = c - 1 - q.1 by omega))), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
    · intro p _
      rw [if_neg (by have := p.2; omega), mul_zero]

end SlopeTestRemainingChoices

open GlobalTheory.SeeSaw.SplitLat (colProj)

theorem auxiliaryLattice_splitsAlongWitt_at_place {A B : HSp D} {c ρ : ℕ} (t : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B A ρ) (hc : c = 2 * ρ)
    (hh : IsAuxiliaryVectorWittDec t d) (hi : d.i₀ = frameMat B A t.ι) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : GlobalTheory.FinPl.Pl D) : MonoAt d (t.lat Λ 𝔟) Λ v := by
  obtain ⟨h2, he, s, he'⟩ := hh
  have hρ : ρ ≤ c := by omega
  have hx : ∀ p : ℕ, ((-D.host.xi0) ^ (p + 1)) ≠ 0 := fun p => pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)
  have hs : ∀ p, s p ≠ 0 := by
    intro p hp
    have h1 := congrFun (congrFun d.e'e p) p
    rw [Matrix.one_apply_eq] at h1
    have hcol : ∀ k, d.e' k p = 0 := fun k => by rw [he']; simp [colsOf, hp]
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol] at h1
  have ha := eq_idempotent_mul_add_of_mul_sub_eq t.a hc hρ s hs
  rw [← he, ← he'] at ha
  have hX : d.qX * t.a = cfE c := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_e',
      Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hY : d.qY * t.a = cfE' c s := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qY_e, GlobalTheory.SeeSaw.SplitLat.qY_e',
      Matrix.one_mul, Matrix.zero_mul, zero_add]
  have h0 : d.q0 * t.a = 0 := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero,
      Matrix.zero_mul, Matrix.zero_mul, add_zero]
  refine monoAt_of_proj d _ _ (fun i => ?_) (fun i => ?_) ?_ ?_ v
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i) 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qX_i₀, colProj_zero]
    · rw [colProj_mul, hX]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he]
      simp only [colProj, Matrix.of_apply, colsOf, cfE]
      by_cases hq : i.1 = q.1
      · have e : (Fin.castLE hρ i : Fin c) = q := Fin.ext hq
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm ((-D.host.xi0) ^ _), mul_assoc, mul_inv_cancel₀ (hx _),
          mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c) := fun e => hq (by rw [e]; rfl)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i : Fin c).rev 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qY_i₀, colProj_zero]
    · rw [colProj_mul, hY]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he']
      simp only [colProj, Matrix.of_apply, colsOf, cfE']
      by_cases hq : q.1 + i.1 + 1 = c
      · have e : (Fin.castLE hρ i : Fin c).rev = q := Fin.ext (by simp [Fin.val_rev]; omega)
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm (s i), mul_assoc, mul_inv_cancel₀ (hs _), mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c).rev := fun e => hq (by rw [e]; simp [Fin.val_rev]; omega)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · exact sumLat_proj d.q0 (by rw [← hi]; exact GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one d) h0
  · intro x hx
    rw [hi]
    exact mem_sumLat_of hx

theorem monoAt_jac : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : GlobalTheory.Asc.Frames G), Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D),
      MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v := by
  intro D T L sc G F hF ρ h v
  have H := auxiliaryLattice_splitsAlongWitt_at_place (G.colDec (2 * ρ + 1) (by omega) (by omega)) (F.dJ ρ h) (by omega) (hF.hJ ρ h) (hF.aJ ρ h)
    (G.Λ (.core (2 * ρ + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) v
  rw [← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)] at H
  exact H

end GlobalTheory.AscFin.MonoJac

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiVertexLatticeSplitsAlongWittAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiVertexLattice_splitsAlongWitt_at_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : GlobalTheory.Asc.Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v := by
  first | exact @GlobalTheory.AscFin.MonoJac.monoAt_jac | exact GlobalTheory.AscFin.MonoJac.monoAt_jac | (intros; apply GlobalTheory.AscFin.MonoJac.monoAt_jac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryDualPairGlobalToLocalTensorTransfer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryDualPairGlobalToLocalTensorTransfer
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobalPair.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.HoweGlobal.Transfer (ext ext_of_mem ext_of_not_mem ext_update ext_vac)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (T : Finset (Pl (F := F)))
  (hvac : ∀ v, M.vac v ∈ SB (Fin n × Fin d → Fv F v))
  (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
include hvac

theorem ext_mem_SB (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : Pl (F := F)) : ext M T φ v ∈ SB _ := by
  by_cases hv : v ∈ T
  · rw [ext_of_mem M T φ ⟨v, hv⟩]; exact (φ ⟨v, hv⟩).2
  · rw [ext_of_not_mem M T φ v hv]; exact hvac v


omit hvac in
include hstd in
theorem ext_std (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [ext_vac M T φ, hstd] with v h1 h2
  rw [h1, h2]


include hstd in
theorem rest_ext (f : SInf F (Fin n × Fin d)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    Rest (evI F) ⇑f (fun x => ∏ᶠ v, ext M T φ v fun i => evFin F v (x i)) :=
  GlobalTheory.ThK.EvUniqInf.rest_pure f _ (ext_mem_SB M T hvac φ) (ext_std M T hstd φ)


include hstd in
theorem acts_ext [DecidableEq T] (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) (z : ↥(SB (Fin n × Fin d → Fv F v.1)))
    (Op : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ)
    (h : Acts (evFin F v.1) Op (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) (z : (Fin n × Fin d → Fv F v.1) → ℂ)) :
    Op (pure f (ext M T φ)) = pure f (ext M T (Function.update φ v z)) := by
  rw [ext_update]
  refine GlobalTheory.ThK.LocalOps.acts_pure v.1 Op f (ext M T φ) _
    (GlobalTheory.TensUniq.pure_mem_schA f _ (ext_mem_SB M T hvac φ) (ext_std M T hstd φ))
    (GlobalTheory.PureFactor.mulSupport_finite _ (ext_std M T hstd φ)) ?_
  simpa only [ext_of_mem] using h

theorem pure_mem_algD {ψ : AddChar (AF F) ℂ} (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ emb) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    pure f (ext M T φ) ∈ GlobalTheory.SquareAgree.algD M ψ emb :=
  Submodule.subset_span ⟨f, ext M T φ, hf, ext_mem_SB M T hvac φ, ext_vac M T φ, rfl⟩

end GlobalTheory.HoweGlobalPair.Transfer

end

noncomputable section

open scoped Classical


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweGlobalPair.Transfer in
open GlobalTheory.HoweGlobal.Transfer (ext ext_of_mem ext_of_not_mem ext_update ext_vac mem_of_pure mem_of_tprod) in
theorem GlobalTheory.HoweGlobalPair.tensor_transfer : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W)
    (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
    (∀ v, M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) →
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ N, GlobalTheory.SquareAgree.IsThetaSubG M ψ emb om N →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) [DecidableEq {v // v ∈ T}]
      (L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] w : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1))) →ₗ[ℂ] ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ w : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') →
      (∀ x ∈ GlobalTheory.HoweGlobalPair.relInf M ψ emb om, ∀ y, L (x ⊗ₜ[ℂ] y) ∈ N) ∧
      (∀ w : T, ∀ x ∈ GlobalTheory.HoweGlobalPair.relFin om w.1, ∀ (x₀ : ↥(M.Pol ψ emb)) (y : ∀ w' : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w'.1))),
          L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y w x)) ∈ N) ∧
      (∀ g ∈ GlobalTheory.HoweGlobalPair.opInf M ψ emb om, ∀ t, L t ∈ N → L (TensorProduct.map g LinearMap.id t) ∈ N) ∧
      (∀ w : T, ∀ g ∈ GlobalTheory.HoweGlobalPair.opFin om w.1, ∀ t, L t ∈ N →
        L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
          (fun w' : T => (LinearMap.id : ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w'.1)) →ₗ[ℂ] _)) w g)) t) ∈ N) := by
  intro F E _ _ _ _ _ σ n d X W M ψ emb om hvac hstd N hN T _ L hL
  have hLe : ∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))),
      L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = pure (f : SInf F (Fin n × Fin d)) (ext M T φ) :=
    fun f φ => hL f φ _ (fun v h => ext_of_mem M T φ ⟨v, h⟩) (fun v h => ext_of_not_mem M T φ v h)
  have hpA := pure_mem_algD M T hvac (ψ := ψ) emb
  have hR := rest_ext M T hvac hstd
  have hSB := ext_mem_SB M T hvac
  have hV := ext_vac M T
  have hLA : ∀ t, L t ∈ GlobalTheory.SquareAgree.algD M ψ emb := by
    intro t
    refine mem_of_pure ((GlobalTheory.SquareAgree.algD M ψ emb).comap L) (fun x φ => ?_) t
    rw [Submodule.mem_comap, hLe]
    exact hpA _ x.2 φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have key : ∀ φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)),
        GlobalTheory.HoweGlobalPair.relInf M ψ emb om ≤ N.comap (L ∘ₗ (TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ φ)) := by
      intro φ
      refine Submodule.span_le.2 ?_
      rintro x (⟨γ, hγ, f, hf, hD⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
      · show L (x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        rw [hLe]
        exact hN.lie γ hγ f hf _ x.2 hD _ (hSB φ) (hV φ)
      · show L ((f₁ - f) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        rw [TensorProduct.sub_tmul, map_sub, hLe, hLe]
        exact hN.cpt k hk _ f.2 _ f₁.2 hA _ (hSB φ) (hV φ)
    intro x hx y
    exact mem_of_tprod (N.comap (L ∘ₗ TensorProduct.mk ℂ _ _ x)) (fun φ => key φ hx) y
  · intro w x hx x₀ y
    rw [hLe]
    refine hN.fin w.1 _ _ x₀.2 (hSB _) (hV _) ?_
    rw [ext_of_mem M T _ w, Function.update_self]
    exact hx
  · intro g hg t ht
    rcases hg with ⟨k, hk, hkA⟩ | ⟨γ, hγ, hgD⟩
    · have e : ∀ t, L (TensorProduct.map g LinearMap.id t) = om (1, k) (L t) := by
        intro t
        refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map g LinearMap.id)
          ((om (1, k)) ∘ₗ L)) (fun x φ => ?_) t)
        refine LinearMap.mem_eqLocus.2 ?_
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact (hkA x _ (hR _ φ)).symm
      rw [e]
      exact hN.stabCpt k hk _ ht
    · let S : Submodule ℂ (↥(M.Pol ψ emb) ⊗[ℂ]
          (⨂[ℂ] v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))) :=
        { carrier := {t | ∀ z, HasDerivAt (fun s : ℝ => om (1, γ (Multiplicative.ofAdd s)) (L t) z)
            (L (TensorProduct.map g LinearMap.id t) z) 0}
          add_mem' := fun {t₁ t₂} h₁ h₂ z => by
            simp only [map_add (f := _), Pi.add_apply]
            exact (h₁ z).add (h₂ z)
          zero_mem' := fun z => by
            simp only [map_zero, Pi.zero_apply]
            exact hasDerivAt_const 0 0
          smul_mem' := fun c t h z => by
            simp only [map_smul, Pi.smul_apply, smul_eq_mul]
            exact (h z).const_mul c }
      have hS : ∀ t, t ∈ S := mem_of_pure S (fun x φ z => by
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact hgD x _ (hR _ φ) z)
      exact hN.stabLie γ hγ _ ht _ (hLA _) (hS t)
  · intro w g hg t ht
    obtain ⟨h, hh, hA⟩ := hg
    have e : ∀ t, L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
        (fun w' : T => (LinearMap.id : ↥(SB (Fin n × Fin d → Fv F w'.1)) →ₗ[ℂ] _)) w g)) t) = om (1, h) (L t) := by
      intro t
      refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update
          (fun w' : T => (LinearMap.id : ↥(SB (Fin n × Fin d → Fv F w'.1)) →ₗ[ℂ] _)) w g)))
          ((om (1, h)) ∘ₗ L)) (fun x φ => ?_) t)
      refine LinearMap.mem_eqLocus.2 ?_
      have hφ : (fun w' => (Function.update
          (fun w' : T => (LinearMap.id : ↥(SB (Fin n × Fin d → Fv F w'.1)) →ₗ[ℂ] _)) w g w') (φ w')) =
          Function.update φ w (g (φ w)) := by
        funext w'
        by_cases hw : w' = w
        · subst hw; simp
        · simp [Function.update_of_ne hw]
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod, hLe]
      rw [hφ, acts_ext M T hvac hstd _ φ w (g (φ w)) _ (hA (φ w))]
    rw [e]
    exact hN.stabFin w.1 h hh _ ht

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryDualPairGlobalToLocalTensorTransferStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDualPair_global_to_local_tensor_transfer : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W)
    (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W),
    (∀ v, M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) →
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ N, GlobalTheory.SquareAgree.IsThetaSubG M ψ emb om N →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))) [DecidableEq {v // v ∈ T}]
      (L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] w : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1))) →ₗ[ℂ] ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ w : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') →
      (∀ x ∈ GlobalTheory.HoweGlobalPair.relInf M ψ emb om, ∀ y, L (x ⊗ₜ[ℂ] y) ∈ N) ∧
      (∀ w : T, ∀ x ∈ GlobalTheory.HoweGlobalPair.relFin om w.1, ∀ (x₀ : ↥(M.Pol ψ emb)) (y : ∀ w' : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w'.1))),
          L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y w x)) ∈ N) ∧
      (∀ g ∈ GlobalTheory.HoweGlobalPair.opInf M ψ emb om, ∀ t, L t ∈ N → L (TensorProduct.map g LinearMap.id t) ∈ N) ∧
      (∀ w : T, ∀ g ∈ GlobalTheory.HoweGlobalPair.opFin om w.1, ∀ t, L t ∈ N →
        L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
          (fun w' : T => (LinearMap.id : ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w'.1)) →ₗ[ℂ] _)) w g)) t) ∈ N) := by
  first | exact @GlobalTheory.HoweGlobalPair.tensor_transfer | exact GlobalTheory.HoweGlobalPair.tensor_transfer | (intros; apply GlobalTheory.HoweGlobalPair.tensor_transfer <;> assumption)
end
end
