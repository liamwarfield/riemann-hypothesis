module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.ReferenceTupleNeBaseTuple
section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.TrueColumnChoicesHeckeCharReferenceEqOne
noncomputable section
section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)

def eExp (D : D7) (j : Fin D.R.m) (g : D.R.Psi) : ℚ := (D.hc (D.eTau.symm g)).e j

structure CharFrame (D : D7) where

  P : PiBar D.host

  W : Omg D.host

  mu0 : Fin D.R.m → HChar D.host.E
  eta : HChar D.host.E
  chiPsi : HChar D.host.E
  del : HChar D.host.E
  del' : HChar D.host.E
  isMu0 : ∀ j, IsMu0 P W (eExp D j) j.1 (mu0 j)
  isEta : IsEtaT D.host eta
  isChi : IsChiPsi D.host chiPsi
  isDel : IsDelta D.host.pde del
  isDel' : IsDelta D.host.pde' del'

def CharFrame.delAt {D : D7} (C : CharFrame D) (l : ℕ) : HChar D.host.E := if l = D.host.pde then C.del' else C.del

structure TupTied (D : D7) (C : CharFrame D) (nch : NChoice D) where

  xi : D.what₂.Tup → HChar D.host.E
  xi_inj : Function.Injective xi
  xi_fin : ∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n
  xi_triv : ∀ μ, (xi μ).TrivOn D.host.F
  xi_tame : ∀ μ v, (xi μ).TameAt v

  psi : D.what₂.places.Pl → HChar D.host.E

  trueColumnChoices_heckeChar_reference_eq_one : xi D.what₂.mu0 = 1

  xi_star : xi D.what₂.muStar = C.del
  xi_star' : xi D.what₂.muStar' = C.del'

  xi_tw : ∀ w, xi (D.what₂.muTw w) = C.delAt (D.what₂.places.resChar w) * psi w

  psi_is : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → IsPsi (D.what₂.places.resChar w) (nch.Q w) (psi w)

  psi_un : ∀ w, D.what₂.muAt w = D.what₂.mu0 → psi w = 1

def IsFinIdele {L : Type} [Field L] [NumberField L] (a : Ideles L) : Prop :=
  ∀ w : InfinitePlace L, (a : AdeleRing (𝓞 L) L).1 w = 1

structure DtTied (D : D7) (C : CharFrame D) where
  eDt : Ideles D.host.E →* D.Dt
  surj : Function.Surjective eDt

  ker_open : IsOpen ((eDt.ker : Subgroup (Ideles D.host.E)) : Set (Ideles D.host.E))
  inf : ∀ w y, eDt (infIdele D.host.E w y) = 1

  onF : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (k : D.host.Fˣ),
    eDt (∏ Q ∈ aboveF (L := D.host.E) D.host.F v, localIdele D.host.E Q (atFin Q (upF D.host.F k))) = 1

  ker_le : ∀ a, eDt a = 1 → ∀ w w', IsConjPl D.host w w' →
    Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 w) = Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 w')

  rat : letI := D.host.cmStar; ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
    eDt (diagUnits D.host.E k) = D.e1Dt z

  UO_eq : ∀ x, x ∈ D.UO ↔ ∃ a : Ideles D.host.E,
    (∀ v, Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 v) = 1) ∧ eDt a = x

  muTil_eq : ∀ (j : Fin D.R.m) (a : Ideles D.host.E), IsFinIdele a → D.muTil (j.1 + 1) (eDt a) = (C.mu0 j).1 a

  chiD_eq : ∀ a : Ideles D.host.E, IsFinIdele a → D.chiD (eDt a) = C.chiPsi.1 a

def IsCSD {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) : Prop :=
  (∀ w w', IsConjPl H w w' → ∀ k : H.Eˣ, χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹) ∧
    ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹

end GlobalTheory.Mem.Chr

end
end
end

noncomputable section

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.Mem.Chr.TieModel

open Formalism.BasicNotions Formalism.FrobeniusOrbits

theorem emb_mul_indep {L I : Type} [Field L] [CharZero L] [Fintype I] (σ : I → L →+* ℂ) (hσ : Function.Injective σ)
    (m : I → ℤ) (h : ∀ k : L, k ≠ 0 → ∏ i, σ i k ^ m i = 1) : m = 0 := by
  classical
  have key : ∀ x : L, ∑ i, (m i : ℂ) * σ i x = 0 := by
    intro x
    let f : ℂ → ℂ := fun t => ∏ i, (1 + t * σ i x) ^ m i
    have hd : ∀ i ∈ (Finset.univ : Finset I),
        HasDerivAt (fun t : ℂ => (1 + t * σ i x) ^ m i) ((m i : ℂ) * σ i x) 0 := by
      intro i _
      have h1 : HasDerivAt (fun t : ℂ => 1 + t * σ i x) (σ i x) 0 := by
        simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (σ i x)).const_add 1
      have h2 := (hasDerivAt_zpow (m i) ((fun t : ℂ => 1 + t * σ i x) 0) (Or.inl (by simp))).comp (0 : ℂ) h1
      simpa [Function.comp_def] using h2
    have hf : HasDerivAt f (∑ i, (m i : ℂ) * σ i x) 0 := by
      have := HasDerivAt.fun_finsetProd hd
      simpa [f] using this
    have hs := hasDerivAt_iff_tendsto_slope.1 hf
    have hu : Tendsto (fun n : ℕ => ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ), Eventually.of_forall fun n => ?_⟩
      exact one_div_ne_zero (Nat.cast_add_one_ne_zero n)
    have hfin : ∀ᶠ n : ℕ in atTop, (1 + (1 / ((n : L) + 1)) * x) ≠ 0 := by
      rw [← Nat.cofinite_eq_atTop]
      refine Set.Subsingleton.finite ?_
      intro a ha b hb
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha hb
      have ha1 : ((a : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero a
      have hb1 : ((b : L) + 1) ≠ 0 := Nat.cast_add_one_ne_zero b
      field_simp at ha hb
      have : (a : L) = b := by linear_combination ha - hb
      exact_mod_cast this
    have h0 : Tendsto (fun n : ℕ => slope f 0 ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' (hfin.mono fun n hn => ?_)
      have h1 := h _ hn
      have h2 : f ((1 : ℂ) / ((n : ℂ) + 1)) = 1 := by
        refine Eq.trans ?_ h1; simp [f]
      have h3 : f 0 = 1 := by simp [f]
      simp only [slope, h2, h3, vsub_self, smul_zero]
    exact tendsto_nhds_unique (hs.comp hu) h0
  have li := (linearIndependent_monoidHom L ℂ).comp (fun i => (σ i : L →* ℂ))
    (fun i j hij => hσ (RingHom.coe_monoidHom_injective hij))
  have := Fintype.linearIndependent_iff.1 li (fun i => (m i : ℂ)) (by
    funext x
    simpa [Finset.sum_apply] using key x)
  funext i
  exact_mod_cast this i

theorem unit_sq (z : ℂ) (hz : z ≠ 0) : (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / starRingEnd ℂ z := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have h2 : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h3 : z * starRingEnd ℂ z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  field_simp
  rw [← h3]

theorem hasInf_unique {L I : Type} [Field L] [NumberField L] [Fintype I] (φ : I → L →+* ℂ) (h1 : Function.Injective φ)
    (h2 : ∀ i j, φ i ≠ (starRingEnd ℂ).comp (φ j)) {χ : HChar L} {n n' : I → ℤ} (h : χ.HasInf φ n) (h' : χ.HasInf φ n') :
    n = n' := by
  let σ : I ⊕ I → L →+* ℂ := Sum.elim φ fun i => (starRingEnd ℂ).comp (φ i)
  have hσ : Function.Injective σ := by
    rintro (i | i) (j | j) hij
    · exact congrArg _ (h1 hij)
    · exact absurd hij (h2 i j)
    · exact absurd hij.symm (h2 j i)
    · refine congrArg _ (h1 (RingHom.ext fun x => ?_))
      have := congrArg (fun f : L →+* ℂ => starRingEnd ℂ (f x)) hij
      simpa [σ] using this
  have := emb_mul_indep σ hσ (Sum.elim (n - n') (n' - n)) (fun k hk => by
    have e := (h (Units.mk0 k hk)).symm.trans (h' (Units.mk0 k hk))
    simp only [Units.val_mk0] at e
    have hne : ∀ i, φ i k ≠ 0 := fun i => by simpa using hk
    have hu : ∀ i, φ i k / ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := fun i =>
      div_ne_zero (hne i) (by exact_mod_cast norm_ne_zero_iff.2 (hne i))
    have e2 : ∏ i, (φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ (n i - n' i) = 1 := by
      simp_rw [zpow_sub₀ (hu _)]
      rw [Finset.prod_div_distrib, e, div_self]
      exact Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hu i)
    have e3 := congrArg (· ^ 2) e2
    simp only [← Finset.prod_pow, one_pow] at e3
    rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib, ← e3]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm (n i - n' i), zpow_mul, zpow_natCast, unit_sq _ (hne i), div_zpow]
    simp only [σ, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply, RingHom.comp_apply]
    rw [div_eq_mul_inv, ← zpow_neg, neg_sub])
  funext i
  have := congrFun this (Sum.inl i)
  simpa [sub_eq_zero] using this

theorem inf_eq_one_of_order {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.1 (infIdele L w y) = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow, map_pow, hx]
  show χ.1 (infDiag k) = 1
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

instance totallyComplexE {R : Ranks} (H : Formalism.BasicNotions.Host R) : IsTotallyComplex H.E := by
  haveI := H.isCMField_hostE
  infer_instance

theorem embTau_inj (D : D7) : Function.Injective (embTau D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem embTau_ne_conj (D : D7) (i j : D.what₂.Tau) : embTau D i ≠ (starRingEnd ℂ).comp (embTau D j) := by
  intro h
  have hi : embTau D i (D.host.sqd) = Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau i).2
  have hj : embTau D j (D.host.sqd) = Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau j).2
  rw [h, RingHom.comp_apply, hj, map_mul, Complex.conj_I, Complex.conj_ofReal] at hi
  have h0 : ((Real.sqrt D.host.d : ℝ) : ℂ) = 0 := by
    have : (2 * Complex.I) * ((Real.sqrt D.host.d : ℝ) : ℂ) = 0 := by linear_combination -hi
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  have : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  exact this.ne' (by exact_mod_cast h0)

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

end GlobalTheory.Mem.Chr.TieModel
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BotWeights

open Formalism.L2.Host (HChar)
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

variable {D : D7}

theorem hasInf_of_chars {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (χ : HChar D.host.E)
    (h : ∀ x, P.W.chV'.f x ^ P.W.ep' = χ.1 (finIdl D x)) :
    χ.HasInf (GlobalTheory.Mem.Chr.embTau D) (fun τ => P.W.ep' * P.W.chV'.n τ) := by
  intro a
  have h1 := χ.2.2 a
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← GlobalTheory.Mem.Col2.SplitChar.finIdl_incU, mul_comm] at h1
  rw [← h (GlobalTheory.NormSum.UnramHecke.incU D a)] at h1
  have h2 := P.W.chV'.aut a
  have h3 : ((χ.inf a : ℂˣ) : ℂ) = (((P.W.chV'.f (GlobalTheory.NormSum.UnramHecke.incU D a) : ℂˣ) : ℂ) ^ P.W.ep')⁻¹ := by
    have := congrArg (Units.val : ℂˣ → ℂ) h1
    rw [Units.val_mul, Units.val_one, Units.val_zpow_eq_zpow_val] at this
    exact eq_inv_of_mul_eq_one_right this
  have hf := eq_inv_of_mul_eq_one_left h2
  rw [h3, hf, inv_zpow, inv_inv, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, mul_comm]
  rfl

end GlobalTheory.BotWeights

namespace GlobalTheory.BotWeights

open Formalism.L2.Host (HChar)

theorem weights_const : GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (i j : Fin D.R.m) (δ t0 : ℂ), ∃ n₀ : D.what₂.Tau → ℕ,
      ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' → P.n = n₀ := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G i j δ t0 => ?_⟩⟩
  have key : ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
      ((Lc.C.mu0 j / G.ch.chiH (D.R.m - i))⁻¹ : HChar D.host.E).HasInf (GlobalTheory.Mem.Chr.embTau D)
        (fun τ => P.W.ep' * P.W.chV'.n τ) := by
    intro s Q P P' hB k
    have h := hasInf_of_chars P _ hB.chars.2 k
    rw [← h]
    obtain ⟨n, hn, ho⟩ := hL.xi_fin s
    have hx := GlobalTheory.Mem.Chr.TieModel.inf_eq_one_of_order hn ho k
    have hx' : (Lc.xiH s).inf k = 1 := hx
    simp only [nuH, div_eq_mul_inv, Formalism.L2.Host.HChar.inf_inv, Formalism.L2.Host.HChar.inf_mul, hx', mul_one]
  by_cases hex : ∃ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P'
  · obtain ⟨s₀, Q₀, P₀, P₀', h₀⟩ := hex
    refine ⟨P₀.n, fun s Q P P' hB => funext fun τ => ?_⟩
    have e := congrFun (GlobalTheory.Mem.Chr.TieModel.hasInf_unique _ (GlobalTheory.Mem.Chr.TieModel.embTau_inj D)
      (GlobalTheory.Mem.Chr.TieModel.embTau_ne_conj D) (key s Q P P' hB) (key s₀ Q₀ P₀ P₀' h₀)) τ
    have w1 := P.wt τ
    have w2 := P₀.wt τ
    have d1 : (P.d : ℤ) = ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by exact_mod_cast hB.rank.2.2.1
    have d2 : (P₀.d : ℤ) = ((botBig D i j + botSmall D i j : ℕ) : ℤ) := by exact_mod_cast h₀.rank.2.2.1
    have : (P.n τ : ℤ) = P₀.n τ := by linarith
    exact_mod_cast this
  · exact ⟨0, fun s Q P P' hB => absurd ⟨s, Q, P, P', hB⟩ hex⟩

end GlobalTheory.BotWeights
