module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraAlt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockComp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

section Points

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

theorem exists_locIn_of_eq {A B : Subalgebra F Ω} (hAB : A = B) (p : Ideal A) (hp : p.IsPrime) :
    ∃ q : Ideal B, q.IsPrime ∧ IndefiniteRowSideFullHecke.Kleiman2.locIn A p = IndefiniteRowSideFullHecke.Kleiman2.locIn B q := by
  subst hAB
  exact ⟨p, hp, rfl⟩

theorem chartRingOver_oneBlock_comp {κ κ' : Type} (σ : κ' ≃ κ) (v : κ → Ω) (c : Unit → κ') :
    chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) c =
      chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) (fun u => σ (c u)) := by
  rw [SectionsOverLocalization.chartRingOver_oneBlock_eq, SectionsOverLocalization.chartRingOver_oneBlock_eq]
  congr 1
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨σ i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by simp⟩


variable (F) in
theorem modelPts_oneBlock_comp {κ κ' : Type} (σ : κ' ≃ κ) (v : κ → Ω) :
    IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) =
      IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) := by
  ext z
  constructor
  · rintro ⟨c, hc, p, hp, rfl⟩
    obtain ⟨q, hq, he⟩ := exists_locIn_of_eq (chartRingOver_oneBlock_comp σ v c) p hp
    exact ⟨fun u => σ (c u), fun u => hc u, q, hq, he⟩
  · rintro ⟨c, hc, p, hp, rfl⟩
    have hc' : ∀ u, IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ) ⟨u, σ.symm (c u)⟩ ≠ 0 := fun u => by
      simpa [IndefiniteRowSideFullHecke.Kleiman2.oneBlock] using hc u
    have hch : chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock v) c =
        chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (v ∘ σ)) (fun u => σ.symm (c u)) := by
      rw [chartRingOver_oneBlock_comp σ v]
      simp
    obtain ⟨q, hq, he⟩ := exists_locIn_of_eq hch p hp
    exact ⟨fun u => σ.symm (c u), hc', q, hq, he⟩


variable (F) in
theorem modelPts_eq_of_base {N : ℕ} {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) (k₀ : K)
    (e : ι k₀ ≃ Fin (N + 1)) {K' : Type} {ι' : K' → Type} (y' : (Σ k, ι' k) → Ω) (k₀' : K')
    (e' : ι' k₀' ≃ Fin (N + 1)) (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀)
    (hy' : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀')
    (hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm) :
    IndefiniteRowSideFullHecke.Kleiman2.modelPts F y = IndefiniteRowSideFullHecke.Kleiman2.modelPts F y' := by
  rw [hy.2, hy'.2, ← modelPts_oneBlock_comp F e.symm, hx, modelPts_oneBlock_comp F e'.symm]

end Points

theorem veryAmple_change (hGen : ModelChangeGen.Statement) (F : Type) [Field F] (Ω : Type) [Field Ω]
    [Algebra F Ω] (N : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (k₀ : K) (e : ι k₀ ≃ Fin (N + 1))
    (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (y' : (Σ k, ι' k) → Ω) (k₀' : K') (e' : ι' k₀' ≃ Fin (N + 1))
    (hy : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y k₀) (hy' : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F y' k₀')
    (hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm)
    (β : K → ℤ) (β' : K' → ℤ)
    (hs : ∀ c : ℤ, secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) =
      secOver F y' (β' + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀')) :
    IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y β ↔ IndefiniteRowSideFullHecke.Kleiman2.VeryAmple F y' β' := by
  have h0 : secOver F y β = secOver F y' β' := by simpa using hs 0
  have hpts := modelPts_eq_of_base F y k₀ e y' k₀' e' hy hy' hx
  unfold IndefiniteRowSideFullHecke.Kleiman2.VeryAmple IndefiniteRowSideFullHecke.Kleiman2.SameModel
  rw [hpts]
  constructor
  · rintro ⟨n, x', hmem, hgen, hsame⟩
    refine ⟨n, x', fun j => h0 ▸ hmem j, ?_, hsame⟩
    exact (hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs n x' hmem).1 hgen
  · rintro ⟨n, x', hmem, hgen, hsame⟩
    have hmem' : ∀ j, x' j ∈ secOver F y β := fun j => h0 ▸ hmem j
    exact ⟨n, x', hmem', (hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs n x' hmem').2 hgen, hsame⟩

theorem VeryAmpleModel.proof (hVA : VeryAmpleEq.Statement) (hGen : ModelChangeGen.Statement) :
    VeryAmpleModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hxe hmod Q β hQ
  subst hxe
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Q
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (Q.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen Q n g := hg
  have hmod' := GraphModel.full F N Ω _ Q n (r + 1) g hx hgen
  have hsec := realises_graph Q n g hgen
  rw [hVA F N Ω _ Q n (r + 1) g hgen]
  exact (veryAmple_change hGen F Ω N K ι y k₀ e (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock
    (Equiv.refl _) hmod hmod' rfl β (graphDeg n) (fun c => (hQ c).symm.trans (hsec c))).symm

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockGenDiagLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)

def BlockGen (S : Type*) [CommRing S] {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) : Prop :=
  ∀ j : ι k₀, y ⟨k₀, j⟩ ≠ 0 → ∀ k, ∃ w : ι k → Ω,
    (∀ a b, y ⟨k, a⟩ * w b ∈
      chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) (fun _ => j)) ∧
      ∑ b, y ⟨k, b⟩ * w b = 1

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def ChartKernel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (Ω : Type) [Field Ω]
    [Algebra S Ω] (y : (Σ k, ι k) → Ω) (Ω' : Type) [Field Ω'] [Algebra S Ω'] (y' : (Σ k, ι k) → Ω'),
    mIdealOver S y ≤ mIdealOver S y' → ∀ c : ∀ k, ι k, (∀ k, y' ⟨k, c k⟩ ≠ 0) →
      ∀ g : MvPolynomial (Σ k, ι k) S, aeval (fun p => y p / y ⟨p.1, c p.1⟩) g = 0 →
        aeval (fun p => y' p / y' ⟨p.1, c p.1⟩) g = 0

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistMulTwistTwistSys
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver)

theorem twistMul_twist_twistSys {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (M : SubSystem S x Ω) (a : ℕ) (m c : ℤ) :
    (twistMul M a m).twist (twistSys S x c) = twistMul M a (m + c) := by
  rw [twistMul, twistMul, SubSystem.twist_assoc, twistSys_twist_eq_add]

theorem ModelVeryAmpleEq.proof (hVA : VeryAmpleEq.Statement) (hMS : ModelMulSecs.Statement)
    (hCh : ModelChangeVeryAmple.Statement) : ModelVeryAmpleEq.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e hmod β Q hQ a m _
  have hx : ∃ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hmod.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  obtain ⟨L, hL⟩ := exists_lineBundle_twistMul Q a m
  obtain ⟨n, hn⟩ := Generated.full.{0, 0} F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) L
  obtain ⟨r, g, -, hg⟩ := GraphClosedAlt.exists_fin_generators
    (L.tensorProd (twistBundle F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) n)) (hn n le_rfl)
  have hgen : IsGraphGen L n g := hg
  have hmod' := GraphModel.full F N Ω _ L n (r + 1) g hx hgen
  have hsec := twist_secs_eq_secOver L n g hgen
  have hH : ∀ c : ℤ, (L.twist (twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).secs =
      secOver F y (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) := by
    intro c
    rw [hL, twistMul_twist_twistSys, hMS F K ι Ω y k₀ N e hmod β Q hQ a (m + c), add_smul, add_assoc]
  rw [← hL, hVA F N Ω _ L n (r + 1) g hgen]
  exact hCh F Ω N (Unit ⊕ Unit) (graphIdx N (r + 1)) _ baseBlock (Equiv.refl _) K ι y k₀ e hmod' hmod rfl
    (graphDeg n) (a • β + m • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) (fun c => (hsec c).symm.trans (hH c))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver secOver)

theorem RealiseRestrict.proof (hG : ModelGenerated.Statement) (hS : SpanSecs.Statement)
    (hR : ResidueMap.Statement) (hRG : ResidueGen.Statement) (hC : RestrictGen.Statement) :
    RealiseRestrict.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy Q β hQ K' _ _ y' hy' hI hxy
  subst hx
  obtain ⟨Q'', hQ''⟩ := BundleOfDeg.full F K ι K' y' k₀ N e hy' β
  obtain ⟨ca, hca⟩ := Kleiman.Generated.full F Ω N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) Q
  obtain ⟨cb, hcb⟩ := Kleiman.Generated.full F K' N (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) Q''
  obtain ⟨cg, hcg⟩ := hG F K ι Ω y k₀ hy β
  obtain ⟨c, hcA, hcB, hcG⟩ : ∃ c, ca ≤ c ∧ cb ≤ c ∧ cg ≤ c :=
    ⟨max ca (max cb cg), by omega, by omega, by omega⟩
  obtain ⟨R, σ, hfr, hblk, hch⟩ := hR F K ι Ω y K' y' hI
  choose d₀ hd₀ using hy'.1
  obtain ⟨ρ, hρ1, hρ2⟩ := hRG F K ι Ω y K' y' hI R σ hfr hch (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) (hcg c hcG) d₀ hd₀

  have hT : ∀ t : K', t ∈ secOver F y' (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) ↔
      ∀ I : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm),
        t ∈ Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) I)
          (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) := by
    intro t
    have h := hS F K ι K' y' k₀ N e _ rfl hy' (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) 0 t
    simp only [PowRealises.twistMod_zero, mul_one, Submodule.mem_iInf, Submodule.restrictScalars_mem,
      neg_zero, zpow_zero] at h
    rw [h, PowRealises.mem_secOver]
    refine forall_congr' fun cc => forall_congr' fun hc => ?_
    rw [hρ2 cc hc, PowRealises.mem_span_inv_iff _
      (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))]
  have hQgen : ∀ I, (Q.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) c)).sub I =
      Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) I)
        (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) := fun I => by
    rw [← hca c hcA I, hQ c]
  have hQ''gen : ∀ I, (Q''.toSubSystem.twist (Kleiman.twistSys F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) c)).sub I =
      Submodule.span (Kleiman.chartRing F (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) I)
        (ρ '' (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω)) := fun I => by
    rw [← hcb c hcB I, hQ'' c]
    apply le_antisymm
    · rw [Submodule.span_le]
      intro t ht
      exact (hT t).mp ht I
    · rw [Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ((hT t).mpr fun J => Submodule.subset_span ht)

  have hfx : ∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m →
      aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) g ≠ 0 →
      ∃ h : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) g ∈ R,
        σ ⟨_, h⟩ = aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) f /
          aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) g := by
    intro f g m hf hg hg0
    obtain ⟨h, hh⟩ := hblk k₀ (rename e.symm f) (rename e.symm g) m hf.rename_isHomogeneous
      hg.rename_isHomogeneous (by rwa [aeval_rename])
    have ea : aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) (rename e.symm f) /
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) (rename e.symm g) =
        aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f / aeval (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) g := by
      rw [aeval_rename, aeval_rename]
    refine ⟨ea ▸ h, ?_⟩
    have hsub : (⟨_, ea ▸ h⟩ : R) = ⟨_, h⟩ := Subtype.ext ea.symm
    rw [hsub, hh, aeval_rename, aeval_rename]
  have hw' : (∏ k, y' ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hd₀ k)
  obtain ⟨r, hr⟩ := hC F N Ω (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) K' (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀ ∘ e.symm) hxy
    R σ hfx Q Q'' c (secOver F y (β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) : Set Ω) ρ
    (∏ k, y ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k))
    (∏ k, y' ⟨k, d₀ k⟩ ^ (-(β + c • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) hw' hQgen hQ''gen hρ1
  exact ⟨Q'', r, hr, hQ''⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremSFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

set_option linter.unusedSectionVars false

namespace KHTheoremSFree

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def Bad (a : (Σ k, ι k) → ℤ) : Prop :=
  ∀ k, negSet a k = ∅ ∨ negSet a k = Finset.univ

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem embed_apply (a : (Σ k, ι k) → ℤ) (n : ℕ) (f : CombC S (negSet a) n) (I : KH.Cell K ι n)
    (h : ∀ k, negSet a k ⊆ I.1 k) : embed S a n f I = f ⟨I, h⟩ • monoFrac S I.1 a := by
  simp [embed, h]
  rfl

theorem embed_mem_cechBc (hE : KHFreeEmbed.Statement) {a : (Σ k, ι k) → ℤ} {c d : K → ℤ}
    (ha : KHFree.blockSum a = c + d) {n : ℕ} {b : CombC S (negSet a) n} (hb : b ∈ combB S (negSet a) n) :
    embed S a n b ∈ KH.cechBc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n := by
  cases n with
  | zero =>
    have hb0 : b = 0 := (Submodule.mem_bot S).mp hb
    subst hb0
    rw [map_zero]
    exact Submodule.zero_mem _
  | succ m =>
    obtain ⟨g, rfl⟩ := LinearMap.mem_range.mp hb
    exact ⟨embed S a m g, (hE S K ι a).2.1 c d ha m g, (hE S K ι a).1 m g⟩

theorem cocycle_decomp (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    {c d : K → ℤ} {n : ℕ} {z : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n}
    (hz : z ∈ KH.cechZc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) :
    ∃ (A : Finset ((Σ k, ι k) → ℤ)) (f : ∀ a : (Σ k, ι k) → ℤ, CombC S (negSet a) n),
      (∀ a ∈ A, KHFree.blockSum a = c + d) ∧ z = ∑ a ∈ A, embed S a n (f a) ∧
        ∀ a ∈ A, combD S (negSet a) n (f a) = 0 := by
  obtain ⟨A, f, hA, rfl⟩ := hD S K ι c d n z hz.1
  refine ⟨A, f, hA, rfl, hI S K ι (n + 1) A (fun a => combD S (negSet a) n (f a)) ?_⟩
  have h0 : KH.cechD S ι _ n (∑ a ∈ A, embed S a n (f a)) = 0 := hz.2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h0
  simpa only [(hE S K ι _).1] using h0

theorem part_cyclic (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement) (a : (Σ k, ι k) → ℤ) {n : ℕ}
    {g : CombC S (negSet a) n} (hg : combD S (negSet a) n g = 0) :
    ∃ s : S, g - s • singOne S (negSet a) n ∈ combB S (negSet a) n ∧ (s ≠ 0 → Bad a) := by
  by_cases hb : Bad a
  · obtain ⟨s, hs⟩ := (hY S K ι (negSet a) n hb).2 g hg
    exact ⟨s, hs, fun _ => hb⟩
  · simp only [Bad, not_forall, not_or] at hb
    obtain ⟨k, hk0, hku⟩ := hb
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ ∉ negSet a k := by
      by_contra h
      push Not at h
      exact hku (Finset.eq_univ_of_forall h)
    obtain ⟨g', hg', hg'I⟩ := hC S K ι (negSet a) n k i₀ hi₀ g hg
    have h0 : g' = 0 := funext fun I => (hg'I I).2 fun h => hk0 h.1
    refine ⟨0, ?_, fun h => absurd rfl h⟩
    rw [zero_smul, sub_zero]
    rwa [h0, sub_zero] at hg'


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem negSet_empty {a : (Σ k, ι k) → ℤ} {e : K → ℤ} (ha : KHFree.blockSum a = e) (he : ∀ k, 0 ≤ e k) (hb : Bad a)
    (k : K) : negSet a k = ∅ := by
  rcases hb k with h | h
  · exact h
  refine Finset.eq_empty_of_forall_notMem fun i _ => ?_
  have hall : ∀ j, a ⟨k, j⟩ < 0 := fun j => by
    have hj : j ∈ negSet a k := h ▸ Finset.mem_univ j
    simpa [negSet] using hj
  have hneg : ∑ j, a ⟨k, j⟩ < 0 := Finset.sum_neg (fun j _ => hall j) ⟨i, Finset.mem_univ _⟩
  have hk : ∑ j, a ⟨k, j⟩ = e k := congrFun ha k
  linarith [he k]

omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem nonneg_of_negSet_empty {a : (Σ k, ι k) → ℤ} (h : ∀ k, negSet a k = ∅) (p : Σ k, ι k) : 0 ≤ a p := by
  by_contra hp
  have hm : p.2 ∈ negSet a p.1 := by simp [negSet]; omega
  rw [h p.1] at hm
  exact Finset.notMem_empty _ hm


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem singOne_eq_zero {J : ∀ k, Finset (ι k)} (hJ : ∀ k, J k = ∅) {n : ℕ} (hn : 1 ≤ n) :
    singOne S J n = 0 := by
  funext I
  simp only [singOne, Pi.zero_apply]
  rw [if_neg]
  intro h
  have h1 : ∀ k, (I.1.1 k).card - 1 = 0 := fun k => by rw [h k (hJ k)]
  have hs := I.1.2.2
  simp only [h1, Finset.sum_const_zero] at hs
  omega


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem singOne_zero {J : ∀ k, Finset (ι k)} (I : CombCell ι J 0) : singOne S J 0 I = 1 := by
  simp only [singOne]
  rw [if_pos]
  intro k _
  have hs := I.1.2.2
  have hk := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
  have hpos := Finset.card_pos.mpr (I.1.2.1 k)
  omega

theorem finite (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement) (hF : KHFreeBadFinite.Statement)
    (d c : K → ℤ) (n : ℕ) :
    Module.Finite S (KH.cechHc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) := by
  classical
  set Z := KH.cechZc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n
  set Bf := (hF K ι (c + d)).toFinset
  have hBf : ∀ a ∈ Bf, KHFree.blockSum a = c + d ∧ Bad a := fun a ha => (hF K ι (c + d)).mem_toFinset.mp ha
  let gen : ((Σ k, ι k) → ℤ) → KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n :=
    fun a => embed S a n (singOne S (negSet a) n)
  have hgen : ∀ a ∈ Bf, gen a ∈ Z := fun a ha =>
    ⟨(hE S K ι a).2.1 c d (hBf a ha).1 n _, by
      change KH.cechD S ι _ n (embed S a n _) = 0
      rw [(hE S K ι a).1, (hY S K ι (negSet a) n (hBf a ha).2).1, map_zero]⟩

  let Ψ : (Bf → S) →ₗ[S] Z :=
    LinearMap.codRestrict Z (∑ x : Bf, (LinearMap.proj x : (Bf → S) →ₗ[S] S).smulRight (gen x.1))
      (fun s => by
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
        exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hgen x.1 x.2))
  have hΨ : ∀ t, (Ψ t : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n) =
      ∑ x : Bf, t x • gen x.1 := fun t => by
    simp only [Ψ, LinearMap.codRestrict_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
  refine Module.Finite.of_surjective ((Submodule.mkQ _).comp Ψ) ?_
  intro x
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨A, f, hA, rfl, hcoc⟩ := cocycle_decomp hE hD hI hz
  choose! s hs hsb using fun a (ha : a ∈ A) => part_cyclic hC hY a (hcoc a ha)
  refine ⟨fun x => if x.1 ∈ A then s x.1 else 0, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq,
    Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, hΨ]
  have hsum : ∑ x : Bf, (if x.1 ∈ A then s x.1 else 0) • gen x.1 = ∑ a ∈ A, s a • gen a := by
    rw [Finset.sum_coe_sort Bf (fun a => (if a ∈ A then s a else 0) • gen a)]
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.inter_comm]
    refine Finset.sum_subset Finset.inter_subset_left fun a ha hna => ?_
    have hs0 : s a = 0 := by
      by_contra h0
      exact hna (Finset.mem_inter.mpr ⟨ha, (hF K ι (c + d)).mem_toFinset.mpr ⟨hA a ha, hsb a ha h0⟩⟩)
    rw [hs0, zero_smul]
  rw [hsum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun a ha => ?_
  have he : embed S a n (f a) - s a • gen a = embed S a n (f a - s a • singOne S (negSet a) n) := by
    rw [map_sub, map_smul]
  rw [he]
  exact embed_mem_cechBc hE (hA a ha) (hs a ha)

theorem vanish (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement)
    (d c : K → ℤ) (n : ℕ) (hn : 1 ≤ n) (hcd : ∀ k, 0 ≤ c k + d k) :
    Subsingleton (KH.cechHc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) := by
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.H1VanishingDevissage.cechHc_subsingleton_iff]
  intro z hz
  obtain ⟨A, f, hA, rfl, hcoc⟩ := cocycle_decomp hE hD hI hz
  refine Submodule.sum_mem _ fun a ha => embed_mem_cechBc hE (hA a ha) ?_
  obtain ⟨s, hs, hsb⟩ := part_cyclic hC hY a (hcoc a ha)
  by_cases h0 : s = 0
  · rwa [h0, zero_smul, sub_zero] at hs
  · have hJ := negSet_empty (hA a ha) (fun k => by simpa using hcd k) (hsb h0)
    rwa [singOne_eq_zero hJ hn, smul_zero, sub_zero] at hs

theorem sections (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement)
    (d c : K → ℤ) (hcd : ∀ k, 0 ≤ c k + d k)
    (z : KH.CechC S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) 0)
    (hz : z ∈ KH.cechZc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c 0) :
    ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d), ∀ I, z I = LocalizedModule.mk m 1 := by
  classical
  obtain ⟨A, f, hA, rfl, hcoc⟩ := cocycle_decomp hE hD hI hz
  have hpart : ∀ a ∈ A, ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d),
      ∀ I, embed S a 0 (f a) I = LocalizedModule.mk m 1 := by
    intro a ha
    obtain ⟨s, hs, hsb⟩ := part_cyclic hC hY a (hcoc a ha)
    have hfa : f a = s • singOne S (negSet a) 0 := sub_eq_zero.mp ((Submodule.mem_bot S).mp hs)
    by_cases h0 : s = 0
    · refine ⟨0, Submodule.zero_mem _, fun I => ?_⟩
      rw [hfa, h0, zero_smul, map_zero, LocalizedModule.zero_mk]
      rfl
    · have hJ := negSet_empty (hA a ha) (fun k => by simpa using hcd k) (hsb h0)
      obtain ⟨m, hm, hmI⟩ := (hE S K ι a).2.2 (nonneg_of_negSet_empty hJ)
      rw [hA a ha] at hm
      refine ⟨s • m, Submodule.smul_mem _ _ hm, fun I => ?_⟩
      have hsub : ∀ k, negSet a k ⊆ I.1 k := fun k => by rw [hJ k]; exact Finset.empty_subset _
      have hval : (s • singOne S (negSet a) 0) ⟨I, hsub⟩ = s := by
        change s * singOne S (negSet a) 0 ⟨I, hsub⟩ = s
        exact (congrArg (s * ·) (singOne_zero _)).trans (mul_one s)
      rw [embed_apply a 0 (f a) I hsub, hfa, hval, hmI, LocalizedModule.smul'_mk]
  choose! m hm hmI using hpart
  refine ⟨∑ a ∈ A, m a, Submodule.sum_mem _ hm, fun I => ?_⟩
  rw [Finset.sum_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← LocalizedModule.mkLinearMap_apply, map_sum]
  exact Finset.sum_congr rfl fun a ha => by rw [hmI a ha, LocalizedModule.mkLinearMap_apply]

end KHTheoremSFree

theorem KHTheoremSFree.proof (hE : KHFreeEmbed.Statement) (hD : KHFreeDecomp.Statement) (hI : KHFreeIndep.Statement)
    (hC : KHCombContract.Statement) (hY : KHCombCyclic.Statement) (hF : KHFreeBadFinite.Statement) :
    KH.TheoremSFreeStatement := by
  intro S _ K _ _ ι _ _ d
  exact ⟨fun c n => KHTheoremSFree.finite hE hD hI hC hY hF d c n,
    fun c n hn hcd => KHTheoremSFree.vanish hE hD hI hC hY d c n hn hcd,
    fun c hcd z hz => KHTheoremSFree.sections hE hD hI hC hY d c hcd z hz⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.QuotPartEqGradedPiece
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial Filter ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc cechZc cechBc cechCc locPart quotPart Cell cellMon)

noncomputable section

theorem quotPart_eq_gradedPiece {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (V : Ideal (MvPolynomial (Σ k, ι k) F)) (m : K → ℤ) (hm : ∀ k, 0 ≤ m k) :
    quotPart F V m = NumbersDVR.gradedPiece V (fun k => (m k).toNat) := by
  have hset : {p : MvPolynomial (Σ k, ι k) F | (∀ k, 0 ≤ m k) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p (fun k => (m k).toNat)} =
      (weightedHomogeneousSubmodule F (NumbersDVR.blockWeight ι) (fun k => (m k).toNat) : Set _) := by
    ext p
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_weightedHomogeneousSubmodule, hm, implies_true, true_and]
    exact (Bridge.isMultiHomog_iff p _).symm
  rw [quotPart, hset, NumbersDVR.gradedPiece]
  conv_rhs => rw [← Submodule.span_eq (weightedHomogeneousSubmodule F _ _), Submodule.map_span]
  rfl

theorem isMultiHomog_one {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRingOver S ι) 0 := by
  intro d hd k
  classical
  rw [mem_support_iff, coeff_one] at hd
  split_ifs at hd with h
  · subst h
    simp
  · exact absurd rfl hd

theorem MultiSerre.proof (hS : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.TheoremSStatement) (hI : SectionMapInj.Statement) :
    MultiSerre.Statement := by
  intro F _ K _ _ ι _ _ V hV
  have hV' : IsMultiHomogIdeal V := (Bridge.isMultiHomogIdeal_iff V).mp hV
  have hG : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.IsMGraded F ι (quotPart F V) :=
    HilbertSamuel.QuotPartGraded.proof F K ι V hV'
  obtain ⟨-, ⟨c₁, h₁⟩, ⟨c₂, h₂⟩, -⟩ :=
    hS F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG
  obtain ⟨c₃, h₃⟩ := hI F K ι (MvPolynomial (Σ k, ι k) F ⧸ V) (quotPart F V) inferInstance inferInstance hG
  filter_upwards [eventually_ge_atTop (fun _ : K => max (max c₁ c₂) (max c₃ 0))] with m hm
  have hk : ∀ k, max (max c₁ c₂) (max c₃ 0) ≤ m k := fun k => hm k
  refine ⟨fun i hi => h₁ m i hi fun k => le_trans (by omega) (hk k), ?_⟩

  let Z := cechZc ι (quotPart F V) m 0
  have hmem : ∀ x ∈ quotPart F V m, (fun _ => LocalizedModule.mk x 1 : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CechC F ι
      (MvPolynomial (Σ k, ι k) F ⧸ V) 0) ∈ Z := by
    intro x hx
    refine HilbertSamuel.GenTwistGenerated.mem_cechZc_zero (fun J => ?_)
      (HilbertSamuel.GenTwistGenerated.cechD_const x)
    refine Submodule.subset_span ⟨x, 1, 0, isMultiHomog_one, ?_, rfl⟩
    convert hx using 2
    ext k
    simp
  let φ : quotPart F V m →ₗ[F] Z :=
    { toFun := fun x => ⟨fun _ => LocalizedModule.mk x.1 1, hmem x.1 x.2⟩
      map_add' := fun x y => by
        ext I
        simp
      map_smul' := fun r x => by
        ext I
        simp [LocalizedModule.smul'_mk] }
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hsub : x.1 - y.1 = 0 := by
      refine h₃ m (fun k => le_trans (by omega) (hk k)) _ (Submodule.sub_mem _ x.2 y.2) fun I => ?_
      have h := congrFun (congrArg Subtype.val hxy) I
      change LocalizedModule.mk x.1 1 = LocalizedModule.mk y.1 1 at h
      change LocalizedModule.mkLinearMap (cellMon F I.1) _ (x.1 - y.1) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr h
    exact Subtype.ext (sub_eq_zero.mp hsub)
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, hzx⟩ := h₂ m (fun k => le_trans (by omega) (hk k)) z hz
    exact ⟨⟨x, hx⟩, Subtype.ext (funext fun I => (hzx I).symm)⟩
  have hbot : (cechBc ι (quotPart F V) m 0).comap (cechZc ι (quotPart F V) m 0).subtype = ⊥ := by
    rw [cechBc, Submodule.comap_bot, Submodule.ker_subtype]
  have e2 : cechHc ι (quotPart F V) m 0 ≃ₗ[F] Z := Submodule.quotEquivOfEqBot _ hbot
  have hm0 : ∀ k, 0 ≤ m k := fun k => le_trans (by omega) (hk k)
  rw [e2.finrank_eq, ← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq, NumbersDVR.hilbFn, if_pos hm0,
    quotPart_eq_gradedPiece V m hm0]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MIdealOverOneHeightslock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)
open GroundTheory.Heights₂.Heights.FieldNumbers (relDim)

section Block

variable {F : Type} [Field F] {K : Type} {ι : K → Type} {L : Type} [Field L] [Algebra F L]

theorem comap_mIdealOver_block (y : (Σ k, ι k) → L) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    (mIdealOver F y).comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) := by
  have h1 : (mConeMapOver F y).comp (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) =
      ((Polynomial.aeval (X k₀ : MvPolynomial K L)).restrictScalars F).comp
        (Kleiman.cone (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [mConeMapOver, Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have h2 : ∀ q : Polynomial L,
      aeval (fun _ : K => (Polynomial.X : Polynomial L)) (Polynomial.aeval (X k₀ : MvPolynomial K L) q) = q :=
    fun q => by rw [← Polynomial.aeval_algHom_apply, aeval_X, Polynomial.aeval_X_left_apply]
  ext f
  rw [Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  change mConeMapOver F y (rename _ f) = 0 ↔ _
  have h := AlgHom.congr_fun h1 f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  constructor
  · intro h0
    rw [← h2 (Kleiman.cone (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) f), h0, map_zero]
  · intro h0
    rw [h0, map_zero]

theorem mIdealOver_oneBlock_block (y : (Σ k, ι k) → L) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) =
      baseComap F k₀ e (mIdealOver F y) := by
  have hcomp : (mConeMapOver F y).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := L) fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  ext f
  rw [baseComap, Ideal.mem_comap]
  change mConeMapOver F _ f = 0 ↔ mConeMapOver F y (rename _ f) = 0
  have h := AlgHom.congr_fun hcomp f
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [h]
  constructor
  · intro h0
    rw [h0, map_zero]
  · intro h0
    exact rename_injective _ (fun a b _ => Subsingleton.elim a b) (h0.trans (map_zero _).symm)

end Block

theorem CurveNumModel.proof (hMP : ModelPoint.Statement) (hRR : RealiseRestrict.Statement)
    (hIR : Kleiman.InterNumRestrict.Statement.{0, 0}) (hNM : NumModel.Statement) (hMC : ModelCurves.Statement) :
    CurveNumModel.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hm Q β hQ W hW hle hrel
  classical
  have := hW.isPrime
  have hWy : mIdealOver F (genPtOf W) = W := mIdealOver_genPtOf W hW.multiHomog
  have hzero : ∀ p, genPtOf W p = 0 ↔ (X p : NumbersDVR.MRing ι F) ∈ W := fun p => by
    rw [← X_mem_mIdealOver_iff (k := F), hWy]
  have hy' : ∀ k, ∃ i, genPtOf W ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hW.relevant k
    exact ⟨i, fun h => hi ((hzero _).mp h)⟩
  have hleW : mIdealOver F y ≤ mIdealOver F (genPtOf W) := hWy.symm ▸ hle
  have hm' := hMP F K ι Ω y k₀ hm _ (genPtOf W) hy' hleW
  have hxy : ∀ i, (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) i ≠ 0 → x i ≠ 0 := fun i h h0 => by
    rw [hx] at h0
    exact h ((hzero ⟨k₀, e.symm i⟩).mpr (hle ((X_mem_mIdealOver_iff y ⟨k₀, e.symm i⟩).mpr h0)))
  obtain ⟨Q', r, hR, hQ'⟩ := hRR F K ι Ω y k₀ N e x hx hm Q β hQ _ (genPtOf W) hm' hleW hxy
  have hpp : Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) =
      W.comap (rename fun a : Fin (N + 1) => (⟨k₀, e.symm a⟩ : Σ k, ι k)) := by
    rw [← comap_mIdealOver_block, hWy]
  have hsub : Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm)
      (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm)) 1 := by
    refine (isSubvar_iff_relDim _ 1).mpr ⟨?_, ?_⟩
    · obtain ⟨i, hi⟩ := hy' k₀
      exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
    · rw [mIdealOver_oneBlock_block, hWy]
      exact ((hMC F K ι Ω y k₀ N e x hx hm 1).1 W hW hle hrel).2.2
  have hxx : Kleiman.primeOf (S := F) x ≤
      Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (genPtOf W) k₀ ∘ e.symm) := by
    rw [hx, ← comap_mIdealOver_block, ← comap_mIdealOver_block]
    exact Ideal.comap_mono hleW
  have h1 := hIR F Ω N x _ _ hxy hxx _ 1 hsub ![Q] ![Q'] (fun _ => r) (fun i => by fin_cases i; exact hR)
  have h2 := hNM F K ι _ (genPtOf W) k₀ N e _ rfl hm' 1 ![Q'] ![β] (fun i => by fin_cases i; exact hQ') hsub
  rw [hWy] at h2
  have e1 : (fun i => (![Q] i).toSubSystem) = ![Q.toSubSystem] := by
    funext i; fin_cases i; rfl
  have e2 : (fun i => (![Q'] i).toSubSystem) = ![Q'.toSubSystem] := by
    funext i; fin_cases i; rfl
  rw [e1, e2] at h1
  rw [e2] at h2
  rw [← h2, h1, hpp]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsPowSmulEqZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon IsMGraded)

namespace SectionMapInj

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def chartMon (S : Type) [CommRing S] (c : ∀ k, ι k) : MRingOver S ι :=
  ∏ k, X ⟨k, c k⟩

def chartCell (c : ∀ k, ι k) : KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

theorem dvd_pow_of_mem_cellMon (c : ∀ k, ι k) {t : MRingOver S ι} (ht : t ∈ cellMon S (chartCell c).1) :
    ∃ n : ℕ, t ∣ chartMon S c ^ n := by
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    rw [show i = c k from Finset.mem_singleton.mp hi]
    exact ⟨1, by rw [pow_one]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)⟩
  | one => exact ⟨0, one_dvd _⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    exact ⟨m + n, by rw [pow_add]; exact mul_dvd_mul hm hn⟩

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]

theorem pow_smul_eq_zero_of_le {r : MRingOver S ι} {y : M} {m n : ℕ} (h : r ^ m • y = 0) (hmn : m ≤ n) :
    r ^ n • y = 0 := by
  rw [← Nat.sub_add_cancel hmn, pow_add, mul_smul, h, smul_zero]

theorem exists_pow_smul_eq_zero (c : ∀ k, ι k) {t : MRingOver S ι} (ht : t ∈ cellMon S (chartCell c).1) {y : M}
    (hy : t • y = 0) : ∃ n : ℕ, chartMon S c ^ n • y = 0 := by
  obtain ⟨n, q, hq⟩ := dvd_pow_of_mem_cellMon c ht
  exact ⟨n, by rw [hq, mul_comm, mul_smul, hy, smul_zero]⟩

theorem exists_chart_dvd (N : ℕ) (μ : (Σ k, ι k) →₀ ℕ) (r : S)
    (hμ : ∀ k, Fintype.card (ι k) * N + 1 ≤ ∑ i, μ ⟨k, i⟩) :
    ∃ c : ∀ k, ι k, chartMon S c ^ N ∣ (monomial μ r : MRingOver S ι) := by
  classical
  have hex : ∀ k, ∃ i, N ≤ μ ⟨k, i⟩ := by
    intro k
    by_contra hne
    simp only [not_exists, not_le] at hne
    have hle : ∑ i, μ ⟨k, i⟩ ≤ ∑ _i : ι k, N := Finset.sum_le_sum fun i _ => (hne i).le
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    have := hμ k
    omega
  choose c hc using hex
  refine ⟨c, ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun q => pow_zero _), Fintype.prod_sigma, chartMon,
    ← Finset.prod_pow]
  refine Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_) _
  exact (pow_dvd_pow _ (hc k)).trans (Finset.dvd_prod_of_mem (fun i => (X ⟨k, i⟩ : MRingOver S ι) ^ μ ⟨k, i⟩)
    (Finset.mem_univ (c k)))

variable [Module S M] [IsScalarTower S (MRingOver S ι) M]

def killedSet (𝓜 : (K → ℤ) → Submodule S M) : Set M :=
  {y | (∃ d, y ∈ 𝓜 d) ∧ ∃ n : ℕ, ∀ c : ∀ k, ι k, chartMon S c ^ n • y = 0}

theorem bound_finset (𝓜 : (K → ℤ) → Submodule S M) (F : Finset M) (hF : (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜) :
    ∃ (D : ℤ) (N : ℕ), ∀ f ∈ F, ∃ d : K → ℤ, f ∈ 𝓜 d ∧ (∀ k, d k ≤ D) ∧
      ∀ c : ∀ k, ι k, chartMon S c ^ N • f = 0 := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty => intro _; exact ⟨0, 0, by simp⟩
  | insert a F ha ih =>
    intro hF
    rw [Finset.coe_insert, Set.insert_subset_iff] at hF
    obtain ⟨D, N, hDN⟩ := ih hF.2
    obtain ⟨⟨d, hd⟩, n, hn⟩ := hF.1
    refine ⟨max D (∑ k, |d k|), max N n, fun f hf => ?_⟩
    rcases Finset.mem_insert.mp hf with rfl | hf
    · refine ⟨d, hd, fun k => ?_, fun c => pow_smul_eq_zero_of_le (hn c) (le_max_right _ _)⟩
      exact ((le_abs_self _).trans (Finset.single_le_sum (f := fun k => |d k|) (fun l _ => abs_nonneg _)
        (Finset.mem_univ k))).trans (le_max_right _ _)
    · obtain ⟨e, he, heD, heN⟩ := hDN f hf
      exact ⟨e, he, fun k => (heD k).trans (le_max_left _ _),
        fun c => pow_smul_eq_zero_of_le (heN c) (le_max_left _ _)⟩

theorem exists_finset_span [IsNoetherian (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) :
    ∃ F : Finset M, (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜 ∧
      ∀ y ∈ killedSet (ι := ι) 𝓜, y ∈ Submodule.span (MRingOver S ι) (↑F : Set M) := by
  classical
  obtain ⟨W, ⟨F, hFH, rfl⟩, hmax⟩ := (set_has_maximal_iff_noetherian (R := MRingOver S ι) (M := M)).mpr ‹_›
    {W | ∃ F : Finset M, (↑F : Set M) ⊆ killedSet (ι := ι) 𝓜 ∧ W = Submodule.span (MRingOver S ι) (↑F : Set M)}
    ⟨_, ∅, by simp, rfl⟩
  refine ⟨F, hFH, fun y hy => ?_⟩
  by_contra hn
  refine hmax (Submodule.span _ ↑(insert y F)) ⟨insert y F, ?_, rfl⟩ ?_
  · rw [Finset.coe_insert]; exact Set.insert_subset hy hFH
  · refine lt_of_le_of_ne (Submodule.span_mono (by simp)) fun h => hn ?_
    rw [h]; exact Submodule.subset_span (by simp)

end SectionMapInj

theorem SectionMapInj.full : SectionMapInj.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 hS hfin hM
  classical
  have := hS
  have : IsNoetherian (MRingOver S ι) M := isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨F, hFH, hspan⟩ := SectionMapInj.exists_finset_span (ι := ι) 𝓜
  obtain ⟨D, N, hDN⟩ := SectionMapInj.bound_finset (ι := ι) 𝓜 F hFH
  set L : ℕ := ∑ k, Fintype.card (ι k) with hL
  refine ⟨D + L * N + 1, fun c hc x hx hloc => ?_⟩
  have hxH : x ∈ SectionMapInj.killedSet (ι := ι) 𝓜 := by
    refine ⟨⟨c, hx⟩, ?_⟩
    have hch : ∀ ch : ∀ k, ι k, ∃ n : ℕ, SectionMapInj.chartMon S ch ^ n • x = 0 := by
      intro ch
      have h := hloc (SectionMapInj.chartCell ch)
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
      obtain ⟨u, hu⟩ := h
      rw [one_smul, one_smul, smul_zero] at hu
      exact SectionMapInj.exists_pow_smul_eq_zero ch u.2 hu
    choose n hn using hch
    exact ⟨Finset.univ.sup n, fun ch =>
      SectionMapInj.pow_smul_eq_zero_of_le (hn ch) (Finset.le_sup (Finset.mem_univ ch))⟩
  obtain ⟨g, -, hg⟩ := Submodule.mem_span_finset.mp (hspan x hxH)
  have hV : x ∈ ⨆ (e : K → ℤ) (_ : e ≠ c), 𝓜 e := by
    rw [← hg]
    refine Submodule.sum_mem _ fun f hf => ?_
    obtain ⟨d, hfd, hdD, hfN⟩ := hDN f hf
    rw [MvPolynomial.as_sum (g f), Finset.sum_smul]
    refine Submodule.sum_mem _ fun μ _ => ?_
    set a : K → ℕ := fun k => ∑ i, μ ⟨k, i⟩ with ha
    have hhom : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial μ (AddMonoidAlgebra.coeff (g f) μ) : MRingOver S ι) a := fun m hm k => by
      rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
    have hmem := hM.2 a d _ f hhom hfd
    by_cases he : (d + fun k => (a k : ℤ)) = c
    · have hdeg : ∀ k, Fintype.card (ι k) * N + 1 ≤ ∑ i, μ ⟨k, i⟩ := by
        intro k
        have h1 := congrFun he k
        have h2 := hc k
        have h3 := hdD k
        have h4 : Fintype.card (ι k) ≤ L :=
          Finset.single_le_sum (f := fun k => Fintype.card (ι k)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        have h5 : ((Fintype.card (ι k) * N : ℕ) : ℤ) ≤ ((L * N : ℕ) : ℤ) := by
          exact_mod_cast Nat.mul_le_mul_right _ h4
        simp only [Pi.add_apply] at h1
        push_cast at h5
        have h6 : ((Fintype.card (ι k) * N + 1 : ℕ) : ℤ) ≤ (a k : ℤ) := by push_cast; linarith
        exact_mod_cast h6
      obtain ⟨ch, q, hq⟩ := SectionMapInj.exists_chart_dvd (S := S) N μ (AddMonoidAlgebra.coeff (g f) μ) hdeg
      rw [hq, mul_comm, mul_smul, hfN ch, smul_zero]
      exact Submodule.zero_mem _
    · exact (le_iSup₂ (f := fun (e : K → ℤ) (_ : e ≠ c) => 𝓜 e) _ he) hmem
  exact Submodule.disjoint_def.mp (hM.1.submodule_iSupIndep c) x hx hV

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
