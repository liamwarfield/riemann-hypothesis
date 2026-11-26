module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyIntegrable
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartHessCompare

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLinear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def linPointMap {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    MRing (stackedBlocks T) →+* MvPolynomial (Option (Fin n)) k :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl _, t⟩ => C (α t) * X none
    | ⟨.inr _, t⟩ => ∑ j, C (M t j) * X (some j)

def linPrime {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    Ideal (MRing (stackedBlocks T)) :=
  RingHom.ker (linPointMap α M)

def LinFormsIndep {T : Type} {k : Type} [Field k] {n : ℕ} (M : T → Fin n → k) : Prop :=
  ∀ w : Fin n → k, (∀ t, ∑ j, M t j * w j = 0) → w = 0

def DualStackedExcLinear.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ E : Ideal (MRing (stackedBlocks T)), IsStackedExc b' a E →
      ∃ (k : Type) (_ : Field k) (_ : Fintype k) (α : T → k) (M : T → Fin i → k),
        Submodule.span ℤ (Set.range α) = ⊤ ∧ LinFormsIndep M ∧ E = linPrime α M ∧
          Fintype.card k = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

def LinPrimeCut.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (k : Type) [Field k] (n : ℕ) (α : T → k) (M : T → Fin (n + 2) → k),
    Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
    ∀ c : T, graphSecond c ∉ linPrime α M →
      ∃ M' : T → Fin (n + 1) → k, LinFormsIndep M' ∧
        divSupp (linPrime α M) (graphSecond c) = {linPrime α M'} ∧
        multAt (linPrime α M ⊔ Ideal.span {graphSecond c}) (linPrime α M') = 1

def LinPrimeBase.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (k : Type) [Field k] (α : T → k) (M : T → Fin 1 → k),
    Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
    ∀ c : (κ : Unit ⊕ Unit) → stackedBlocks T κ,
      (∀ κ, (X ⟨κ, c κ⟩ : MRing (stackedBlocks T)) ∉ linPrime α M) →
      Nonempty ((MRing (stackedBlocks T) ⧸ (linPrime α M ⊔
        Ideal.span (Set.range fun κ => (X ⟨κ, c κ⟩ : MRing (stackedBlocks T)) - 1))) ≃+* k)

namespace LinPrimeExample

theorem linPointMap_first {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k)
    (t : T) : linPointMap α M (graphFirst t) = C (α t) * X none := by
  simp [linPointMap, graphFirst]

theorem linPointMap_second {T : Type} [Fintype T] {k : Type} [Field k] {n : ℕ} (α : T → k) (M : T → Fin n → k)
    (t : T) : linPointMap α M (graphSecond t) = ∑ j, C (M t j) * X (some j) := by
  simp [linPointMap, graphSecond]

end LinPrimeExample

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualStdModelField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

noncomputable section

abbrev dualStdModelField (K : Type) [Field K] (i : ℕ) : Type :=
  FractionRing (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))

def dualStdModelS (K : Type) [Field K] (i : ℕ) : dualStdModelField K i :=
  algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _ (C (X ()))

def dualStdModelT (K : Type) [Field K] (i : ℕ) : dualStdModelField K i :=
  algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _ (X ())

def dualStdModelEmb (K : Type) [Field K] (i : ℕ) : ProjField K i →+* dualStdModelField K i :=
  (algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _).comp
    ((C : MvPolynomial Unit (ProjField K i) →+* _).comp C)

def dualStdModelPt {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) :
    (Σ k, Sum.elim (dualBlocks T) (PBlk i) k) → dualStdModelField K i
  | ⟨Sum.inl (), t⟩ => dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i
  | ⟨Sum.inr (), j⟩ =>
    dualStdModelEmb K i (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)) * dualStdModelS K i *
      dualStdModelT K i

def GenFibreModelTransport.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type)
    [∀ k, Fintype (ι' k)] (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P')
    (Ω : Type) [Field Ω] (z : (Σ k', ι' k') → Ω), RingHom.ker (eval₂Hom (Int.castRingHom Ω) z : MRing ι' →+* Ω) = P' →
    ∀ (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ Ω], (algebraMap Φ₀ Ω).fieldRange = Subfield.closure (Set.range (z ∘ v)) →
    ∀ (τ : Type) (w : τ → Σ k', ι' k') (q : Σ k', ι' k'),
      (G.x' q = 0 ↔ z q = 0) ∧
      Module.finrank G.Φ (Algebra.adjoin G.Φ (Set.range fun t => G.x' (w t) / G.x' q)) =
        Module.finrank Φ₀ (Algebra.adjoin Φ₀ (Set.range fun t => z (w t) / z q)) ∧
      (Transcendental (Algebra.adjoin G.Φ (Set.range fun t => G.x' (w t) / G.x' q)) (G.x' q) ↔
        Transcendental (Algebra.adjoin Φ₀ (Set.range fun t => z (w t) / z q)) (z q))

def DualStdGraphModel.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    RingHom.ker (eval₂Hom (Int.castRingHom (dualStdModelField K i)) (dualStdModelPt b) :
        MRing (Sum.elim (dualBlocks T) (PBlk i)) →+* dualStdModelField K i) =
      graphIdeal (dualIdeal b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b))

def DualStdModelRank.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ (dualStdModelField K i)],
    (algebraMap Φ₀ (dualStdModelField K i)).fieldRange =
      Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) →
    1 ≤ i → ∀ c : T,
      dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) ≠ 0 ∧
      Module.finrank Φ₀ (Algebra.adjoin Φ₀ (Set.range fun t : T =>
        dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) = Module.finrank ℚ K

def DualStdModelTransc.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ (dualStdModelField K i)],
    (algebraMap Φ₀ (dualStdModelField K i)).fieldRange =
      Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) →
    1 ≤ i → ∀ c : T,
      Transcendental (Algebra.adjoin Φ₀ (Set.range fun t : T =>
        dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)))
        (dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyCocycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyCocycleAlt

variable {e : ℕ}

def dens (s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : (Fin e → ℂ) → ℝ :=
  maDensity (fun j => hermChartPot (s j))

def pairing (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) : ℝ :=
  ∫ y, (hermChartPot X y - hermChartPot Y y) * dens s y

def blocks {α : Type*} (a b c : α) (i j : ℕ) : Fin e → α :=
  fun s => if (s : ℕ) < i then a else if (s : ℕ) < i + j then b else c

theorem blocks_posDef {M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (hN : N.PosDef)
    (hP : P.PosDef) (i j : ℕ) (s : Fin e) : (blocks M N P i j s).PosDef := by
  unfold blocks
  split_ifs
  exacts [hM, hN, hP]

theorem update_posDef {T : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hT : ∀ j, (T j).PosDef) (p : Fin e)
    {X : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (s : Fin e) : (Function.update T p X s).PosDef := by
  rw [Function.update_apply]
  split_ifs
  exacts [hX, hT s]

theorem integrable_pairing {X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    {s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) :
    Integrable (fun y : Fin e → ℂ => (hermChartPot X y - hermChartPot Y y) * dens s y) := by
  have hCmp := HermFormCompare.proof
  have hHess := ChartHessCompare.proof hCmp
  choose C hC using fun j => hHess e (s j) Y (hs j) hY
  obtain ⟨C₀, hC₀⟩ := hHess e Y Y hY hY
  obtain ⟨K, hK⟩ := ChartEnergyIntegrableAlt.pot_sub_bound hCmp hX hY
  set C' : ℝ := 1 + ∑ j, |C j| with hC'
  have hCj : ∀ j, C j ≤ C' := fun j => by
    have h1 := Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 := le_abs_self (C j)
    linarith
  have hbound : ∀ y, ‖dens s y‖ ≤ C' ^ e * maDensity (fun _ : Fin e => hermChartPot Y) y := by
    intro y
    set HN := cxHessian (hermChartPot Y) y with hHN
    set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => cxHessian (hermChartPot (s j)) y with hAdef
    set B : Fin e → Matrix (Fin e) (Fin e) ℂ := fun _ => ((C' : ℝ) : ℂ) • HN with hBdef
    have hNp : HN.PosSemidef := (hC₀ y).1.posSemidef
    have hApsd : ∀ j, (A j).PosSemidef := fun j => (hC j y).1.posSemidef
    have hAB : ∀ j, (B j - A j).PosSemidef := fun j => by
      have h : ((C' : ℝ) : ℂ) • HN - A j = (((C j : ℝ) : ℂ) • HN - A j) + (((C' - C j : ℝ)) : ℂ) • HN := by
        push_cast
        rw [sub_smul]
        abel
      show (((C' : ℝ) : ℂ) • HN - A j).PosSemidef
      rw [h]
      exact (hC j y).2.add (hNp.smul (Complex.zero_le_real.2 (sub_nonneg.2 (hCj j))))
    have hmono : (mixedDisc A).re ≤ (mixedDisc B).re := ReciprocityTheory.AnForm.A.mdisc_re_mono A B hApsd hAB
    have hnn : 0 ≤ (mixedDisc A).re := (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef A hApsd).2
    have hB : mixedDisc B = ((C' : ℝ) : ℂ) ^ e * HN.det := by
      have h := ReciprocityTheory.AnForm.A.mdisc_const (((C' : ℝ) : ℂ) • HN)
      rw [det_smul, Fintype.card_fin] at h
      exact h
    have hN1 : mixedDisc (fun _ : Fin e => HN) = HN.det := ReciprocityTheory.AnForm.A.mdisc_const HN
    have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
    have hd : dens s y = (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re := rfl
    have hd0 : maDensity (fun _ : Fin e => hermChartPot Y) y =
        (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc (fun _ : Fin e => HN)).re := rfl
    rw [hd, hd0, hN1, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc, abs_of_nonneg hnn]
    rw [hB, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hmono
    calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc A).re
        ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (C' ^ e * HN.det.re) :=
          mul_le_mul_of_nonneg_left hmono hc
      _ = _ := by ring
  have hmeas : Measurable (dens s) := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adb_measurable_maDensity _
  have hmix : Integrable (dens s) :=
    Integrable.mono' ((ChartDensityIntegrable.proof e Y hY).const_mul (C' ^ e)) hmeas.aestronglyMeasurable
      (Eventually.of_forall hbound)
  exact hmix.bdd_mul ((ChartEnergyIntegrableAlt.measurable_hermChartPot X).sub
    (ChartEnergyIntegrableAlt.measurable_hermChartPot Y)).aestronglyMeasurable (Eventually.of_forall hK)

theorem pairing_add {X Y Z : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef) (hZ : Z.PosDef)
    {s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) :
    pairing X Z s = pairing X Y s + pairing Y Z s := by
  unfold pairing
  rw [← integral_add (integrable_pairing hX hY hs) (integrable_pairing hY hZ hs)]
  congr 1
  funext y
  ring

theorem pairing_sub {X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hX : X.PosDef) (hY : Y.PosDef)
    {s t : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hs : ∀ j, (s j).PosDef) (ht : ∀ j, (t j).PosDef) :
    pairing X Y s - pairing X Y t = ∫ y, (hermChartPot X y - hermChartPot Y y) * (dens s y - dens t y) := by
  unfold pairing
  rw [← integral_sub (integrable_pairing hX hY hs) (integrable_pairing hX hY ht)]
  congr 1
  funext y
  ring

theorem pairing_perm (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (s : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (σ : Equiv.Perm (Fin e)) : pairing X Y (s ∘ σ) = pairing X Y s := by
  unfold pairing
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [dens]
  rw [show (fun j => hermChartPot ((s ∘ σ) j)) = (fun j => hermChartPot (s j)) ∘ σ from rfl,
    Inter.maDensity_comp_perm]

theorem step (hS : ChartEnergySymm.Statement) {M N P : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef)
    (hN : N.PosDef) (hP : P.PosDef) {k j : ℕ} (h : k + j < e) :
    pairing M N (blocks M N P k j) - pairing M N (blocks M N P k (j + 1)) =
      -(pairing N P (blocks M N P (k + 1) j) - pairing N P (blocks M N P k (j + 1))) := by
  obtain ⟨p, hpv⟩ : ∃ p : Fin e, (p : ℕ) = k + j := ⟨⟨k + j, h⟩, rfl⟩
  obtain ⟨q, hqv⟩ : ∃ q : Fin e, (q : ℕ) = k := ⟨⟨k, by omega⟩, rfl⟩
  set T := blocks M N P k (j + 1) with hTdef
  have hT : ∀ s, (T s).PosDef := blocks_posDef hM hN hP k (j + 1)
  have hTP : Function.update T p P = blocks M N P k j := by
    funext s
    simp only [Function.update_apply, hTdef, blocks, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  have hTN : Function.update T p N = T := by
    funext s
    simp only [Function.update_apply, hTdef, blocks, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  have key : ∀ s : Fin e, ((Equiv.swap q p s : Fin e) : ℕ) =
      if (s : ℕ) = k then k + j else if (s : ℕ) = k + j then k else s := by
    intro s
    rw [Equiv.swap_apply_def]
    split_ifs <;> (try simp only [Fin.ext_iff] at *) <;> omega
  have hTM : Function.update T p M ∘ Equiv.swap q p = blocks M N P (k + 1) j := by
    funext s
    simp only [Function.comp_apply, Function.update_apply, hTdef, blocks, Fin.ext_iff, key]
    split_ifs <;> first | rfl | omega
  have hsym := hS e M N N P T p hM hN hN hP hT
  have e1 : pairing M N (Function.update T p N) - pairing M N (Function.update T p P) =
      pairing N P (Function.update T p M) - pairing N P (Function.update T p N) := by
    rw [pairing_sub hM hN (update_posDef hT p hN) (update_posDef hT p hP),
      pairing_sub hN hP (update_posDef hT p hM) (update_posDef hT p hN)]
    exact hsym
  rw [← pairing_perm N P (Function.update T p M) (Equiv.swap q p), hTM, hTP, hTN] at e1
  linarith

theorem antidiag_telescope (g : ℕ → ℕ → ℝ) : ∀ e : ℕ,
    ∑ k ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) =
      ∑ k ∈ Finset.range (e + 1), (g k 0 - g 0 k)
  | 0 => by simp
  | e + 1 => by
    have ih := antidiag_telescope g e
    have h1 : ∀ k ∈ Finset.range (e + 1), ∑ j ∈ Finset.range (e + 1 - k), (g (k + 1) j - g k (j + 1)) =
        ∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) + (g (k + 1) (e - k) - g k (e - k + 1)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show e + 1 - k = e - k + 1 by omega, Finset.sum_range_succ]
    have h2 : ∑ k ∈ Finset.range (e + 1), (g (k + 1) (e - k) - g k (e - k + 1)) = g (e + 1) 0 - g 0 (e + 1) := by
      have h3 := Finset.sum_range_sub (fun k => g k (e + 1 - k)) (e + 1)
      simp only [Nat.sub_self, Nat.sub_zero] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [show e + 1 - (k + 1) = e - k by omega, show e + 1 - k = e - k + 1 by omega]
    rw [Finset.sum_range_succ _ (e + 1), Finset.sum_range_succ (fun k => g k 0 - g 0 k) (e + 1), ← ih,
      Nat.sub_self, Finset.sum_range_zero, add_zero, Finset.sum_congr rfl h1, Finset.sum_add_distrib, h2]

theorem chartMixedEnergy_eq (X Y : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (k : ℕ) :
    chartMixedEnergy X Y k = pairing X Y (fun s : Fin e => if (s : ℕ) < k then X else Y) := by
  unfold chartMixedEnergy pairing dens
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  congr 2
  funext j
  by_cases h : (j : ℕ) < k <;> simp [h]

end ChartEnergyCocycleAlt


open ChartEnergyCocycleAlt in
theorem ChartEnergyCocycle.proof (hS : ChartEnergySymm.Statement) : ChartEnergyCocycle.Statement := by
  intro e M N P hM hN hP
  have hb := blocks_posDef hM hN hP
  set g : ℕ → ℕ → ℝ := fun i j => pairing N P (blocks M N P i j) with hg
  have e1 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy M P k =
      pairing M N (blocks M N P k 0) + g k 0 := by
    intro k _
    rw [chartMixedEnergy_eq, hg]
    have : (fun s : Fin e => if (s : ℕ) < k then M else P) = blocks M N P k 0 := by
      funext s
      simp only [blocks, add_zero]
      split_ifs <;> rfl
    rw [this]
    exact pairing_add hM hN hP (hb k 0)
  have e2 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy M N k = pairing M N (blocks M N P k (e - k)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [chartMixedEnergy_eq]
    congr 1
    funext s
    have := s.isLt
    simp only [blocks]
    split_ifs <;> first | rfl | omega
  have e3 : ∀ k ∈ Finset.range (e + 1), chartMixedEnergy N P k = g 0 k := by
    intro k _
    rw [chartMixedEnergy_eq, hg]
    congr 1
    funext s
    simp [blocks]
  have tele : ∀ k ∈ Finset.range (e + 1),
      pairing M N (blocks M N P k 0) - pairing M N (blocks M N P k (e - k)) =
        -∑ j ∈ Finset.range (e - k), (g (k + 1) j - g k (j + 1)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← Finset.sum_range_sub' (fun j => pairing M N (blocks M N P k j)), ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    exact step hS hM hN hP (by omega)
  have hsum : ∑ k ∈ Finset.range (e + 1), (pairing M N (blocks M N P k 0) -
      pairing M N (blocks M N P k (e - k))) = -∑ k ∈ Finset.range (e + 1), (g k 0 - g 0 k) := by
    rw [Finset.sum_congr rfl tele, Finset.sum_neg_distrib, antidiag_telescope]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3, Finset.sum_add_distrib]
  simp only [Finset.sum_sub_distrib] at hsum
  linarith

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PSectionQuotFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SectionQuotientFinite

variable {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')


omit [Fintype T] in
theorem mem_blockFnField_of_mem_chartRingZ (t : T) {b : K'} (hb : b ∈ chartRingZ y (fun _ => t)) :
    b ∈ blockFnField y := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨(), t⟩, rfl, rfl⟩
  | algebraMap r => rw [eq_intCast]; exact intCast_mem _ r
  | add x z _ _ hx hz => exact add_mem hx hz
  | mul x z _ _ hx hz => exact mul_mem hx hz

theorem exists_int_mul_coord_mem : ∃ D : ℤ, D ≠ 0 ∧ ∀ t : T, (D : K') * y ⟨(), t⟩ ∈ integralClosure ℤ K' := by
  classical
  obtain ⟨D, hD0, hD⟩ := exists_integral_multiples ℤ ℚ (L := K') (Finset.univ.image fun t => y ⟨(), t⟩)
  refine ⟨D, hD0, fun t => ?_⟩
  have h := hD (y ⟨(), t⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  rw [zsmul_eq_mul] at h
  exact h

theorem int_mul_mem_of_mem_sectionMod (hy : IsArithVar (mCoordIdeal y) 1) {D : ℤ}
    (hD : ∀ t : T, (D : K') * y ⟨(), t⟩ ∈ integralClosure ℤ K') {m : K'} (hm : m ∈ sectionMod y) :
    (D : K') * m ∈ integralClosure ℤ K' := by
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  suffices hv : ∀ v : HeightOneSpectrum (𝓞 K'), v.valuation K' ((D : K') * m) ≤ 1 by
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K') K' _ hv
    rw [← hr]
    exact r.2
  intro v
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => v.valuation K' (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  have hmt : m / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
    SectionIndexNormAlt.mem_chartLat_iff.mp hm t hyt
  have h1 : v.valuation K' (m / y ⟨(), t⟩) ≤ 1 :=
    (Valuation.mem_integer_iff _ _).mp
      (CurveAffineCharts.mem_integer_of_mem_chartRingZ y v t (fun u => ht u (Finset.mem_univ _)) hmt)
  have h2 : v.valuation K' ((D : K') * y ⟨(), t⟩) ≤ 1 := by
    obtain ⟨r, hr⟩ : ∃ r : 𝓞 K', algebraMap (𝓞 K') K' r = (D : K') * y ⟨(), t⟩ :=
      ⟨⟨_, hD t⟩, rfl⟩
    rw [← hr]
    exact HeightOneSpectrum.valuation_le_one v r
  have e : (D : K') * m = m / y ⟨(), t⟩ * ((D : K') * y ⟨(), t⟩) := by
    field_simp
  rw [e, map_mul]
  exact mul_le_one' h1 h2

theorem fg_sectionMod (hy : IsArithVar (mCoordIdeal y) 1) : AddGroup.FG (sectionMod y) := by
  obtain ⟨D, hD0, hD⟩ := exists_int_mul_coord_mem y
  have : Module.Finite ℤ (integralClosure ℤ K') := inferInstanceAs (Module.Finite ℤ (𝓞 K'))
  let f : sectionMod y →+ integralClosure ℤ K' :=
    { toFun := fun m => ⟨(D : K') * m, int_mul_mem_of_mem_sectionMod y hy hD m.2⟩
      map_zero' := Subtype.ext (mul_zero _)
      map_add' := fun a b => Subtype.ext (mul_add _ _ _) }
  have hinj : Function.Injective f := fun a b h => by
    have h' : (D : K') * a = (D : K') * b := congrArg (fun z : integralClosure ℤ K' => (z : K')) h
    exact Subtype.ext (mul_left_cancel₀ (Int.cast_ne_zero.mpr hD0) h')
  have hfin : Module.Finite ℤ (sectionMod y) := Module.Finite.of_injective f.toIntLinearMap hinj
  exact Module.Finite.iff_addGroup_fg.mp hfin


omit [NumberField K'] in
theorem aeval_ne_zero {s : MRing (fun _ : Unit => T)} (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1))
    (hsP : s ∉ mCoordIdeal y) : aeval y s ≠ 0 := by
  intro h0
  apply hsP
  change s ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
  rw [h0, map_zero, zero_mul]

theorem exists_nat_mul_mem_span (hy : IsArithVar (mCoordIdeal y) 1) {s : MRing (fun _ : Unit => T)}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) {m : K'} (hm : m ∈ sectionMod y) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : K') * m ∈ Submodule.span (curveRing y) {aeval y s} := by
  set x := aeval y s with hxdef
  have hx0 : x ≠ 0 := aeval_ne_zero y hs hsP
  obtain ⟨t, ht⟩ := CurveAffineCharts.exists_chart y hy
  have hmt : m / y ⟨(), t⟩ ∈ blockFnField y :=
    mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.mem_chartLat_iff.mp hm t ht)
  have hxt : x / y ⟨(), t⟩ ∈ blockFnField y :=
    mem_blockFnField_of_mem_chartRingZ y t (SectionIndexNormAlt.aeval_div_mem hs t)
  have hq : m / x ∈ blockFnField y := by
    have e : m / x = (m / y ⟨(), t⟩) / (x / y ⟨(), t⟩) := by
      field_simp
    rw [e]
    exact div_mem hmt hxt
  obtain ⟨n, hn, hnq⟩ := CurveAffineCharts.exists_nat_mul_mem_curveRing y hq
  refine ⟨n, hn, Submodule.mem_span_singleton.mpr ⟨⟨_, hnq⟩, ?_⟩⟩
  rw [Subring.smul_def, smul_eq_mul]
  field_simp

theorem isTorsion (hy : IsArithVar (mCoordIdeal y) 1) {s : MRing (fun _ : Unit => T)}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s (fun _ => 1)) (hsP : s ∉ mCoordIdeal y) (q : sectionQuot y (aeval y s)) :
    ∃ n : ℕ, n ≠ 0 ∧ n • q = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn, hnm⟩ := exists_nat_mul_mem_span y hy hs hsP m.2
  refine ⟨n, hn, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rw [Submodule.subtype_apply]
  simpa [nsmul_eq_mul] using hnm

end SectionQuotientFinite


open SectionQuotientFinite in
theorem SectionQuotFinite.closed : SectionQuotFinite.Statement := by
  intro T _ K' _ _ y s hy hs hsP
  have hfg : AddGroup.FG (sectionQuot y (aeval y s)) :=
    AddGroup.fg_of_surjective (f := (Submodule.mkQ _).toAddMonoidHom) (Submodule.mkQ_surjective _)
      (hG := fg_sectionMod y hy)
  let _ : Module ℤ (sectionQuot y (aeval y s)) := AddCommGroup.toIntModule _
  have hfin : Module.Finite ℤ (sectionQuot y (aeval y s)) := Module.Finite.iff_addGroup_fg.mpr hfg
  refine Module.finite_of_fg_torsion _ fun q => ?_
  obtain ⟨n, hn, hnq⟩ := isTorsion y hy hs hsP q
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)⟩, ?_⟩
  change ((n : ℤ)) • q = 0
  rw [natCast_zsmul]
  exact hnq

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial

namespace StandardDualBaseChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem isMultiHomog_linForm (A : ∀ _ : Unit, Fin i → T → ℤ) (q : Σ _ : Unit, Fin i) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := dualBlocks T) (ι₂ := PBlk i) A q) fun _ => 1 := by
  classical
  intro m hm k
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at ht
  have hmt := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
  subst hmt
  cases k
  simp [Finsupp.single_apply]


omit [DecidableEq T] in
theorem exists_linForm_not_mem (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (hP : IsArithVar (dualIdeal b) i)
    (hBP : IsBasePtFree (K₂ := Unit) (ι₂ := PBlk i) (dualIdeal b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b))) :
    ∀ k₂ : Unit, ∃ j, ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨k₂, j⟩ ∉ dualIdeal b := by
  intro k₂
  by_contra hall
  simp only [not_exists, not_not] at hall
  obtain ⟨-, ⟨hprime, -, hrel⟩, -, -⟩ := hP
  obtain ⟨t, ht⟩ := hrel ()
  obtain ⟨N, hN⟩ := hBP k₂ fun _ => t
  have hle : Ideal.span (Set.range fun j : Fin i =>
      ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b) ⟨k₂, j⟩) ≤ dualIdeal b :=
    Ideal.span_le.mpr (Set.range_subset_iff.mpr hall)
  rw [sup_eq_left.mpr hle, Fintype.prod_unique] at hN
  exact ht (hprime.mem_of_pow_mem N hN)

end StandardDualBaseChange


open StandardDualBaseChange in
theorem DualStdBaseChange.proof (hCM : ChangeOfModelStatement) (hGr : GraphStatement)
    (hGF : GenFibreExistsStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hBP : DualStdBasePtFree.Statement) (hIm : DualStdImageBot.Statement)
    (hDeg : DualStdGenDeg.Statement) (hMet : DualStdMetricPull.Statement) :
    DualStdBaseChange.Statement := by
  intro K _ _ i T _ _ b hb II hi hII
  have hP : IsArithVar (dualIdeal b) i :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K i _ T b hi
  have hBPb := hBP K i T b
  have hGraph := (hGr Unit (dualBlocks T) Unit (PBlk i) (dualIdeal b) i
    (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b)) (fun _ _ => 1) hP
    (isMultiHomog_linForm _) (exists_linForm_not_mem b hP hBPb)).1
  obtain ⟨G⟩ := hGF Unit (PBlk i) (Unit ⊕ Unit) (Sum.elim (dualBlocks T) (PBlk i)) Sum.inr inrV _ i
    isBlockMap_inr hGraph
  obtain ⟨J, hJ, -⟩ := hEU G.Φ _ (fibreIdx (Sum.elim (dualBlocks T) (PBlk i)) (Sum.inr : Unit → Unit ⊕ Unit))
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hbot : IsArithVar (imageZ (inrV (ι := dualBlocks T) (ι₂ := PBlk (n + 1)))
      (graphIdeal (dualIdeal b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk (n + 1)) (dualStdCoordMat b)))) (n + 1) := by
    rw [hIm K (n + 1) T b]
    exact IndefiniteRowSideFullHecke.Inter.isArithVar_bot n
  have key := hCM II hII Unit (dualBlocks T) (PBlk (n + 1)) (dualIdeal b) (n + 1) (dualStdCoordMat b) G J
    (fun _ => fsMulti (PBlk (n + 1))) (fun _ => dualLine (HermLattice.standard K (n + 1)) b hb)
    hP hBPb hbot hJ (fun _ => FsLineSmooth.proof Unit (PBlk (n + 1)))
    (fun _ => (DualLineSemipositive.proof K (n + 1) _ T b hb).1) (fun _ => rfl)
    (fun _ z hz => hMet K (n + 1) T b hb z hz)
  rw [key, hDeg K (n + 1) T b G J hi hJ, hIm K (n + 1) T b]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedGraphFibre

variable {K' : Type} [Fintype K'] {ι : K' → Type} [∀ k, Fintype (ι k)]


open Classical in
def vertWeight {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then 0 else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)

theorem vertR_eq_finsum (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    vertR P L s = ∑ᶠ W, (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℝ) * vertWeight L W := by
  classical
  rw [vertR, finsum_mem_def]
  refine finsum_congr fun W => ?_
  simp only [Set.indicator, ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, vertWeight]
  by_cases hW : W ∈ divSupp P s
  · rw [if_pos hW, if_pos hW]
  · rw [if_neg hW, if_neg hW, Nat.cast_zero, zero_mul]

theorem finite_support (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    (Function.support fun W => (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℝ) * vertWeight L W).Finite :=
  (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s).support.finite_toSet.subset fun W hW =>
    Finsupp.mem_support_iff.mpr fun h0 => hW (by simp [h0])

theorem vertR_sub (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s₁ s₂ : MRing ι)
    (E : Ideal (MRing ι)) (hhor : ¬ IsHorizontal E)
    (hE : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₂ E : ℤ) = ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₁ E + 1)
    (hW : ∀ W, ¬ IsHorizontal W → W ≠ E → ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₂ W = ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₁ W) :
    vertR P L s₁ - vertR P L s₂ = -((geoNum n E (fun j => (L j).a) : ℝ) * Real.log (charOf E)) := by
  classical
  rw [vertR_eq_finsum, vertR_eq_finsum, ← finsum_sub_distrib (finite_support P L s₁) (finite_support P L s₂)]
  have hpt : ∀ W, (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₁ W : ℝ) * vertWeight L W - (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₂ W : ℝ) * vertWeight L W =
      if W = E then -vertWeight L E else 0 := by
    intro W
    by_cases hWh : IsHorizontal W
    · have hne : W ≠ E := fun h => hhor (h ▸ hWh)
      simp [vertWeight, hWh, hne]
    · by_cases hWE : W = E
      · subst hWE
        have hR : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₂ W : ℝ) = ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s₁ W + 1 := by exact_mod_cast hE
        rw [if_pos rfl, hR]
        ring
      · rw [if_neg hWE, hW W hWh hWE, sub_self]
  rw [finsum_congr hpt, finsum_eq_single _ E (fun W hW => if_neg hW), if_pos rfl]
  simp [vertWeight, hhor]

end StackedGraphFibre


open StackedGraphFibre in
theorem DualStackedGraphFibre.proof (hCyc : DualStackedExcCycle.Statement)
    (hSec : DualStackedExcGeoSecond.Statement) (hFir : DualStackedExcGeoFirst.Statement) :
    DualStackedGraphFibre.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab t L hL
  obtain ⟨E, hE, hhor, hEt⟩ := hCyc K i F F' T b b' a hi hlt hcov hab
  have key := vertR_sub (stackedGraph b' a) L (graphSecond t) (C (a t) * graphFirst t) E hhor (hEt t).1
    (hEt t).2
  have ha : ∀ s, a s ≠ 0 := fun s hs =>
    b.ne_zero s (Subtype.ext (by rw [hab s, hs, zero_smul]; rfl))
  refine ⟨fun hall => ?_, fun ⟨j, hj⟩ => ?_⟩
  · have hd : (fun j => (L j).a) = fun _ => degSecond := funext hall
    rw [key, hd, hSec K i F F' T b b' a hi hlt hcov hab E hE, ← DualLatticeIndex.proof K i F F' hlt.le,
      DualStackedDegreeAlt.relIndex_stacked hlt.le b b' a hab,
      Real.log_prod (fun s _ => abs_ne_zero.mpr (Int.cast_ne_zero.mpr (ha s)))]
  · rw [key, hFir K i F F' T b b' a hi hlt hcov hab E hE (fun j => (L j).a) hL ⟨j, hj⟩]
    simp

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopMetricChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 NumberField

noncomputable section

namespace TopDualMetricChange

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]

theorem hermLine_ext {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T)}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A; cases B; cases ha; cases hh; rfl

theorem dualLine_h_zero (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : (Σ _ : Unit, T) → ℂ)
    (hz : ¬ ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0) : (dualLine F b hb).h z = 0 := by
  have h0 : (fun t => z ⟨(), t⟩) = 0 := by
    funext t; by_contra h; exact hz fun _ => ⟨t, h⟩
  show Real.sqrt (dualNormSq b hb fun t => z ⟨(), t⟩) = 0
  rw [h0]
  simp [dualNormSq, ← Pi.zero_def]

def weight (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : ((Σ _ : Unit, T) → ℂ) → ℝ :=
  fun z => Real.log ((dualLine F.withStdMetric b hb).h z) - Real.log ((dualLine F b hb).h z)

theorem weight_hom (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    ∀ (c : Unit → ℂ) z, (∀ k, c k ≠ 0) → weight F b hb (fun p => c p.1 * z p) = weight F b hb z := by
  intro c z hc
  by_cases hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0
  · simp only [weight]
    rw [(dualLine F.withStdMetric b hb).smul c z hc, (dualLine F b hb).smul c z hc]
    have ha : (dualLine F.withStdMetric b hb).a = (dualLine F b hb).a := rfl
    have hs : 0 < ∏ k, ‖c k‖ ^ (dualLine F b hb).a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
    rw [ha, Real.log_mul hs.ne' ((dualLine F.withStdMetric b hb).pos z hz).ne',
      Real.log_mul hs.ne' ((dualLine F b hb).pos z hz).ne']
    ring
  · have hz0 : ∀ p, z p = 0 := by
      rintro ⟨k, t⟩; by_contra h; exact hz fun _ => ⟨t, h⟩
    congr 1; funext p; simp [hz0 p]

theorem weight_smooth (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) : SmoothFn (weight F b hb) :=
  ((DualLineSemipositive.proof K i F.withStdMetric T b hb).1.log fun z hz =>
      ((dualLine F.withStdMetric b hb).pos z hz).ne').sub
    ((DualLineSemipositive.proof K i F T b hb).1.log fun z hz => ((dualLine F b hb).pos z hz).ne')

theorem dualLine_eq_tensor (F : HermLattice K i) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    dualLine F b hb = (dualLine F.withStdMetric b hb).tensor
      (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight (weight F b hb) (weight_hom F b hb)) := by
  refine hermLine_ext (funext fun _ => by simp [ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight, dualLine]) ?_
  funext z
  show (dualLine F b hb).h z = (dualLine F.withStdMetric b hb).h z * Real.exp (-weight F b hb z)
  by_cases hz : ∀ k : Unit, ∃ t, z ⟨k, t⟩ ≠ 0
  · have h1 := (dualLine F.withStdMetric b hb).pos z hz
    have h2 := (dualLine F b hb).pos z hz
    rw [weight, neg_sub, Real.exp_sub, Real.exp_log h1, Real.exp_log h2]
    field_simp
  · rw [dualLine_h_zero F b hb z hz, dualLine_h_zero F.withStdMetric b hb z hz, zero_mul]

theorem ptsIntegral_neg {κ : Type} [Fintype κ] {ι : κ → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ (fun z => -g z) = -ptsIntegral P φ g := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp [neg_mul]
  unfold ptsIntegral ptsIntegralAt
  split_ifs
  · rw [← MeasureTheory.integral_neg]
    simp only [hs, finsum_neg_distrib]
  · simp

theorem degree_withStdMetric_sub (F : HermLattice K i) :
    F.withStdMetric.degree - F.degree = 1 / 2 * ∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re := by
  simp only [HermLattice.degree, subDegree, HermLattice.withStdMetric, IndefiniteRowSideFullHecke.Kernels.gramAt_single,
    Matrix.det_one, Complex.one_re, Real.log_one, Finset.sum_const_zero, mul_zero, sub_zero]
  ring

end TopDualMetricChange


open TopDualMetricChange in
theorem DualTopMetricChange.proof (hTel : TelescopeStatement) (hEnergy : DualMetricEnergy.Statement) :
    DualTopMetricChange.Statement := by
  intro K _ _ i F T _ _ b hb II hi hII
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hP : IsArithVar (dualIdeal b) (n + 1) :=
    DualArithVar.proof (CoordConeArithVar.proof IntDomainDim.proof) K (n + 1) F T b hi
  have hT := hTel Unit (dualBlocks T) (II Unit (dualBlocks T)) (hII Unit (dualBlocks T)) (dualIdeal b) n
    (dualLine F.withStdMetric b hb) (weight F b hb) (weight_hom F b hb) hP
    (DualLineSemipositive.proof K (n + 1) F.withStdMetric T b hb).1 (weight_smooth F b hb)
  rw [← dualLine_eq_tensor F b hb] at hT
  have hw : weight F b hb = fun z =>
      -(Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) := by
    funext z; simp only [weight]; ring
  rw [hw] at hT
  simp only [ptsIntegral_neg, Finset.sum_neg_distrib, neg_neg] at hT
  have hE : ∑ k ∈ Finset.range (n + 1),
      ptsIntegral (dualIdeal b)
        (pot fun j : Fin n => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
        (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
      1 / 2 * (∑ σ : K →+* ℂ, Real.log (F.metric σ).det.re) *
        geomDeg (grassIdeal 1 1 (n + 1 - 1)) (fsMulti (plBlocks 1 1 (n + 1 - 1))) (1 * 1 * (n + 1 - 1)) :=
    hEnergy K (n + 1) F T b hb hi
  rw [degree_withStdMetric_sub F]
  linarith

end

end GroundTheory.Heights₂.Heights
end
