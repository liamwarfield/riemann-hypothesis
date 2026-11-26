module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MeasurablePhiInv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CovolBR
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowBlockCovol : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (b : Fin D.R.rS),
    Countable (cLat X u (Sum.inl (Sum.inr b))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inl (Sum.inr b)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inl (Sum.inr b)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inr b)) F = ENNReal.ofReal (cVal X u (Sum.inl (Sum.inr b)))

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EmbVHomInjective
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def sigI : InfinitePlace X.B.I.F ≃ {w : InfinitePlace D.host.E // w.IsComplex} :=
  X.pl.trans (Formalism.MainNotions.BlockEstimateWords.l2Pl D)

theorem embS_sig (v : InfinitePlace X.B.I.F) :
    embS D (X.pl v) = (sigI X v).1.embedding ∨
      embS D (X.pl v) = ComplexEmbedding.conjugate (sigI X v).1.embedding := by
  have h : (sigI X v).1 = InfinitePlace.mk (embS D (X.pl v)) := rfl
  rcases InfinitePlace.embedding_mk_eq (embS D (X.pl v)) with h1 | h1
  · left; rw [h, h1]
  · right; rw [h, h1]
    ext x; simp

theorem discrE_eq : discr D.host.E = discr D.host.F ^ 2 := D.host.der.discr_sq

theorem finrank_O : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]; exact D.sp.cm.deg2

theorem absNorm_ddS_ideal :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) =
      (discr D.host.F).natAbs ^ 2 := by
  rw [Ideal.absNorm_algebraMap, NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F), finrank_O]

theorem absNorm_ddS : FractionalIdeal.absNorm (ddS D) = (((discr D.host.F).natAbs ^ 2 : ℕ) : ℚ) := by
  unfold ddS
  rw [FractionalIdeal.coeIdeal_absNorm, absNorm_ddS_ideal]

def fHom : X.B.I.F →+* D.host.F where
  toFun := fun a => ⟨X.ιE (algebraMap X.B.I.F X.B.I.E a), (X.ιE_F _).2 ⟨a, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp
  map_zero' := by ext; simp
  map_add' := fun a b => by ext; simp

def fIso : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective (fHom X)
    ⟨fun a b h => by
        have h1 := congrArg Subtype.val h
        exact (algebraMap X.B.I.F X.B.I.E).injective (X.ιE.injective h1),
     fun y => by
        obtain ⟨a, ha⟩ := (X.ιE_F y.1).1 y.2
        exact ⟨a, Subtype.ext ha⟩⟩

theorem discrF_eq : discr X.B.I.F = discr D.host.F := discr_eq_discr_of_ringEquiv X.B.I.F (fIso X)

theorem absDiscrE : |(discr D.host.E : ℝ)| = |(discr X.B.I.F : ℝ)| ^ 2 := by
  rw [discrE_eq, discrF_eq]; push_cast; rw [abs_pow]

theorem sqrtDiscrE : √|(discr D.host.E : ℝ)| = |(discr X.B.I.F : ℝ)| := by
  rw [absDiscrE, Real.sqrt_sq (abs_nonneg _)]

theorem dF_pos : 0 < |(discr X.B.I.F : ℝ)| :=
  abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)

def embVHom : D.host.E →+ (InfinitePlace X.B.I.F → ℂ) where
  toFun := embV X
  map_zero' := by funext v; simp [embV]
  map_add' := fun a b => by funext v; simp [embV]

theorem embVHom_apply (t : D.host.E) : embVHom X t = fun v => embS D (X.pl v) t := rfl

theorem embVHom_injective : Function.Injective (embVHom X) := by
  intro a b h
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  exact (embS D (X.pl v)).injective (congrFun h v)

theorem closure_embV (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    AddSubgroup.closure (embV X '' (I : Set D.host.E)) =
      ((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup).map (embVHom X) := by
  have e : embV X '' (I : Set D.host.E) =
      embVHom X '' (((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup : AddSubgroup D.host.E) : Set D.host.E) := rfl
  rw [e]
  rw [← AddMonoidHom.map_closure, AddSubgroup.closure_eq]

theorem mem_closure_embV (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (a : InfinitePlace X.B.I.F → ℂ) :
    a ∈ AddSubgroup.closure (embV X '' (I : Set D.host.E)) ↔ ∃ t ∈ I, embVHom X t = a := by
  rw [closure_embV, AddSubgroup.mem_map]
  rfl

theorem idealBlock (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hI : I ≠ 0) :
    Countable (AddSubgroup.closure (embV X '' (I : Set D.host.E))) ∧
    (∃ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F ∧
      ∀ v, ∃! a : AddSubgroup.closure (embV X '' (I : Set D.host.E)), (a : InfinitePlace X.B.I.F → ℂ) + v ∈ F) ∧
    ∀ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F →
      (∀ v, ∃! a : AddSubgroup.closure (embV X '' (I : Set D.host.E)), (a : InfinitePlace X.B.I.F → ℂ) + v ∈ F) →
        volume F = ENNReal.ofReal ((FractionalIdeal.absNorm I : ℝ) * 2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
          |(discr X.B.I.F : ℝ)|) := by
  classical
  set C := AddSubgroup.closure (embV X '' (I : Set D.host.E)) with hC
  set ΛE : AddSubgroup D.host.E := (I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup with hΛE
  set Iu : (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ := Units.mk0 I hI with hIu
  have hIu' : ((Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) = I := rfl
  set φ : InfinitePlace X.B.I.F → (D.host.E →+* ℂ) := fun v => embS D (X.pl v) with hφ
  have hsig : ∀ v, φ v = (sigI X v).1.embedding ∨ φ v = ComplexEmbedding.conjugate (sigI X v).1.embedding :=
    fun v => embS_sig X v
  have hΛ : ∀ a ∈ ΛE, a ∈ (Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := fun a ha => ha
  have hk : ΛE.relIndex
      (((Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup)
      = 1 := by
    rw [hIu']; exact AddSubgroup.relIndex_self ΛE
  have hmemC : ∀ a, a ∈ C ↔ ∃ t ∈ I, embVHom X t = a := mem_closure_embV X I

  have hto : ∀ F : Set (InfinitePlace X.B.I.F → ℂ), ∀ v,
      (∃! a : ΛE, (fun i => (1 : ℂ) * φ i a) + v ∈ F) → ∃! b : C, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F := by
    intro F v ⟨a, ha, hu⟩
    refine ⟨⟨embVHom X a, (hmemC _).2 ⟨a, a.2, rfl⟩⟩, ?_, ?_⟩
    · simpa [embVHom_apply, hφ] using ha
    · rintro ⟨b, hb⟩ hbF
      obtain ⟨t, ht, rfl⟩ := (hmemC b).1 hb
      have := hu ⟨t, ht⟩ (by simpa [embVHom_apply, hφ] using hbF)
      subst this
      rfl
  have hfrom : ∀ F : Set (InfinitePlace X.B.I.F → ℂ), ∀ v,
      (∃! b : C, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F) → ∃! a : ΛE, (fun i => (1 : ℂ) * φ i a) + v ∈ F := by
    intro F v ⟨⟨b, hb⟩, hbF, hu⟩
    obtain ⟨t, ht, rfl⟩ := (hmemC b).1 hb
    refine ⟨⟨t, ht⟩, by simpa [embVHom_apply, hφ] using hbF, ?_⟩
    rintro ⟨a, ha⟩ haF
    have := hu ⟨embVHom X a, (hmemC _).2 ⟨a, ha, rfl⟩⟩ (by simpa [embVHom_apply, hφ] using haF)
    have h2 : embVHom X a = embVHom X t := congrArg Subtype.val this
    exact Subtype.ext (embVHom_injective X h2)
  refine ⟨?_, ?_, ?_⟩
  · have : Countable D.host.E := by
      let b := Module.finBasis ℚ D.host.E
      exact Function.Injective.countable b.equivFun.injective
    rw [hC, closure_embV]
    exact Function.Surjective.countable
      (f := fun a : ΛE => (⟨embVHom X a, AddSubgroup.mem_map_of_mem _ a.2⟩ : ΛE.map (embVHom X)))
      (fun ⟨y, hy⟩ => by obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hy; exact ⟨⟨a, ha⟩, rfl⟩)
  · obtain ⟨F, hF, hFd⟩ := Formalism.L2.SG.NGCut.SplitEmbedding.exists_fd D.host.E (InfinitePlace X.B.I.F) φ (sigI X) hsig Iu ΛE hΛ
      (by rw [hk]; exact one_ne_zero) 1 one_ne_zero
    exact ⟨F, hF, fun v => hto F v (hFd v)⟩
  · intro F hF hFd
    have h := Formalism.L2.SG.NGCut.SplitEmbedding.idealCovolC D.host.E (InfinitePlace X.B.I.F) φ (sigI X) hsig Iu ΛE hΛ 1 hk
      one_ne_zero 1 one_ne_zero F hF (fun v => hfrom F v (hFd v))
    rw [h, hIu', sqrtDiscrE X]
    congr 1
    simp

theorem dF_natAbs : |(discr X.B.I.F : ℝ)| = ((discr D.host.F).natAbs : ℝ) := by
  rw [discrF_eq, Nat.cast_natAbs, Int.cast_abs]

theorem absNorm_aaD (a : Fin D.R.rS) :
    ((FractionalIdeal.absNorm (aaD D a) : ℚ) : ℝ) = |(discr X.B.I.F : ℝ)| ^ (-(2 * ((D.R.rS : ℝ) - (a : ℕ)))) := by
  unfold aaD
  rw [map_zpow₀, absNorm_ddS, Rat.cast_zpow, dF_natAbs X]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

theorem aaD_ne_zero (Y : HidaSetting D) (a : Fin D.R.rS) : aaD D a ≠ 0 := by
  intro h
  have h1 := absNorm_aaD Y a
  rw [h, map_zero, Rat.cast_zero] at h1
  have := Real.rpow_pos_of_pos (dF_pos Y) (-(2 * ((D.R.rS : ℝ) - (a : ℕ))))
  linarith

theorem rpow_combine {d : ℝ} (hd : 0 < d) {x y z : ℝ} (h : x + y + 1 = z) : d ^ x * d ^ y * d = d ^ z := by
  rw [← h, Real.rpow_add hd, Real.rpow_add hd, Real.rpow_one]

theorem blockCovol_X (u : D.what₂.Word) (p : LsNc5.LtPair D.R.rS) :
    Countable (cLat X u (Sum.inl (Sum.inl p))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inl (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inl (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p)) F = ENNReal.ofReal (cVal X u (Sum.inl (Sum.inl p))) := by
  have hI : aaD D p.1.1 * (aaD D p.1.2)⁻¹ ≠ 0 := mul_ne_zero (aaD_ne_zero X _) (inv_ne_zero (aaD_ne_zero X _))
  obtain ⟨h1, h2, h3⟩ := idealBlock X _ hI
  refine ⟨h1, h2, fun F hF hFd => (h3 F hF hFd).trans ?_⟩
  congr 1
  show _ = (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((p.1.2 : ℕ) - (p.1.1 : ℕ) : ℝ))
  rw [map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, absNorm_aaD X, absNorm_aaD X, ← Real.rpow_neg (abs_nonneg _)]
  rw [show ∀ a b c e : ℝ, a * b * c * e = (a * b * e) * c by intros; ring, rpow_combine (dF_pos X)]
  · ring
  · ring

theorem blockCovol_K (u : D.what₂.Word) (p : LsNc5.LtPair D.R.rS) :
    Countable (cLat X u (Sum.inr (Sum.inl p))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inr (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inr (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p)) F = ENNReal.ofReal (cVal X u (Sum.inr (Sum.inl p))) := by
  have hI : aaD D p.1.1 * aaD D p.1.2 ≠ 0 := mul_ne_zero (aaD_ne_zero X _) (aaD_ne_zero X _)
  obtain ⟨h1, h2, h3⟩ := idealBlock X _ hI
  refine ⟨h1, h2, fun F hF hFd => (h3 F hF hFd).trans ?_⟩
  congr 1
  show _ = (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((D.R.rS : ℝ) - (p.1.1 : ℕ)) - 2 * ((D.R.rS : ℝ) - (p.1.2 : ℕ)))
  rw [map_mul, Rat.cast_mul, absNorm_aaD X, absNorm_aaD X]
  rw [show ∀ a b c e : ℝ, a * b * c * e = (a * b * e) * c by intros; ring, rpow_combine (dF_pos X)]
  · ring
  · ring

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameRow
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RefNMapKapL
noncomputable section

open MeasureTheory Matrix NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf
  Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut

theorem det_LyM {r k : ℕ} {T : ℝ} (hT : 0 < T) : LinearMap.det (LyM (k := k) (r := r) T) = T ^ r := by
  rw [LyM, LinearMap.det_toLin', Matrix.det_diagonal]
  simp only [Fintype.prod_sum_type, dY, Finset.prod_const_one, one_mul, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [show r * 2 = 2 * r by ring, pow_mul, Real.sq_sqrt hT.le]

theorem refN_map_kapL {n r k : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ)
    (w : Fin k → Fin n → ℂ) (z : Fin n → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hww : ∀ a b, hJ ε (w a) (w b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (w a) = 0) (hfw : ∀ c a, hJ ε (f c) (w a) = 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hzw : ∀ a, hJ ε z (w a) = 0) :
    AEMeasurable (kapL ε e f w z) (refNg hn ε e f w (z0v T z)) ∧
      (refNg hn ε e f w (z0v T z)).map (kapL ε e f w z) =
        ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k) * (T ^ r)⁻¹) • volume := by
  subst hn
  have hFJ := isFrameJ_of hT hee hff hef hww hew hfw hez hfz hzz hzw
  have emb := embQ hFJ
  have hQz : Qm e f w (z0v T z) *ᵥ zBv k r T = z := Qm_zB hT z
  set Ψ := cM (ε := ε) (Qi ε e f w (z0v T z)) (Qm e f w (z0v T z)) with hΨ
  let Φ : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => WlocSk.NB.phi0 t.1 t.2
  have hΦc : Continuous Φ := WlocSk.NB.continuous_nilpotent_chart
  let ψ : Mt k r → (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) := fun x => (WlocSk.NB.psiC x, WlocSk.NB.psiR x)
  have hψc : Continuous ψ := WlocSk.NB.continuous_psiC.prodMk WlocSk.NB.continuous_psiR
  have hleft : Function.LeftInverse ψ Φ := fun t => by
    obtain ⟨h1, h2⟩ := WlocSk.NB.nilpotent_chart_right_inverse t.1 t.2
    show (WlocSk.NB.psiC (WlocSk.NB.phi0 t.1 t.2), WlocSk.NB.psiR (WlocSk.NB.phi0 t.1 t.2)) = t
    rw [h1, h2]
  have hΦe : MeasurableEmbedding Φ := by
    refine MeasurableEmbedding.of_measurable_inverse hΦc.measurable ?_ hψc.measurable hleft
    have hr : Set.range Φ = {x | Φ (ψ x) = x} := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        show Φ (ψ (Φ t)) = Φ t
        rw [hleft t]
      · intro hx
        exact ⟨ψ x, hx⟩
    rw [hr]
    exact (isClosed_eq (hΦc.comp hψc) continuous_id).measurableSet
  have hΦN : ∀ t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ), WlocSk.NB.phi0 t.1 t.2 ∈ Nset k r := fun t =>
    WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2
  set ν := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))).map Φ with hν
  haveI : SigmaFinite ν := hΦe.sigmaFinite_map
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [hν, Measure.map_eq_zero_iff hΦe.measurable.aemeasurable] at h0
    exact isOpen_univ.measure_ne_zero (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))) Set.univ_nonempty
      (by rw [h0, Measure.coe_zero, Pi.zero_apply])
  have hrange : ∀ t, ∃ g : Formalism.REAL.UJ ε, Ψ g = Φ t := fun t => by
    refine ⟨toUJ _ (conjQ_UJ hFJ (hΦN t).1), ?_⟩
    show (Qi ε e f w (z0v T z) * uMat (toUJ _ (conjQ_UJ hFJ (hΦN t).1)) * Qm e f w (z0v T z) :
      Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2
    rw [uMat_toUJ, Qi_Qm_conj hFJ]
  set lam0 := Measure.comap Ψ ν with hlam0
  have hmap : lam0.map Ψ = ν := by
    rw [hlam0, emb.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff, hν, hΦe.map_apply]
    convert measure_empty (μ := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))))
    ext t
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    obtain ⟨g, hg⟩ := hrange t
    exact ⟨g, hg⟩
  haveI : SigmaFinite lam0 := SigmaFinite.of_map _ emb.measurable.aemeasurable (by rw [hmap]; infer_instance)
  have hNz : NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) = NLoc ε e z := by rw [hQz]
  have hz0 : ∃ t : ℂ, z0v T z = t • (Qm e f w (z0v T z) *ᵥ zBv k r T) :=
    ⟨(((Real.sqrt T)⁻¹ : ℝ) : ℂ), by rw [hQz]; rfl⟩
  have hHaar : IsHaarLoc (NLoc ε e z) lam0 := by
    refine ⟨inferInstance, fun h0 => hν0 (by rw [← hmap, h0, Measure.map_zero]), ?_, fun s hs => ?_⟩
    · rw [hlam0, emb.comap_apply, hν, hΦe.map_apply]
      convert measure_empty (μ := (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))))
      ext t
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false,
        not_exists, not_and]
      intro g hg hgt
      apply hg
      rw [← hNz]
      refine inN_of_conj hFJ (inWb_zB T) ?_
      have : (Qi ε e f w (z0v T z) * uMat g * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = WlocSk.NB.phi0 t.1 t.2 := hgt
      rw [this]; exact hΦN t
    · have hs' : InN ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) (uMat s) := by
        have h1 : s ∈ NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) := by rw [hNz]; exact hs
        exact h1
      have h0 : Qi ε e f w (z0v T z) * uMat s * Qm e f w (z0v T z) ∈ Nset k r :=
        conj_mem_Nset hFJ hz0 (uMat_mem s) hs'
      set m0 := Qi ε e f w (z0v T z) * uMat s * Qm e f w (z0v T z) with hm0
      have hfun : Ψ ∘ (fun x => s * x) = lmulM m0 ∘ Ψ := by
        funext x
        show (Qi ε e f w (z0v T z) * uMat (s * x) * Qm e f w (z0v T z) :
          Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
          m0 * (Qi ε e f w (z0v T z) * uMat x * Qm e f w (z0v T z))
        rw [uMat_mul, hm0]
        simp only [← Matrix.mul_assoc]
        rw [Matrix.mul_assoc (Qi ε e f w (z0v T z) * uMat s) (Qm e f w (z0v T z)) (Qi ε e f w (z0v T z)),
          Qm_mul_Qi hFJ, Matrix.mul_one]
      have hsh : lmulM m0 ∘ Φ = Φ ∘ (fun t : (WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ) =>
          (t.1 + WlocSk.NB.shG m0 t.1, t.2 + WlocSk.NB.shH m0 t.1)) := by
        funext t
        obtain ⟨h1, h2⟩ := WlocSk.NB.lmul_coord h0 t.1 t.2
        have hmem := WlocSk.UnitaryGroupBasics.mem_n_mul h0 (WlocSk.NB.test_vector_mem_schwartz_bruhat t.1 t.2)
        show m0 * WlocSk.NB.phi0 t.1 t.2 =
          WlocSk.NB.phi0 (t.1 + WlocSk.NB.shG m0 t.1) (t.2 + WlocSk.NB.shH m0 t.1)
        rw [← h1, ← h2]
        exact (WlocSk.NB.nilpotent_chart_left_inverse hmem).symm
      have hmp := WlocSk.NB.shear_mp (d := r) WlocSk.NB.rk (WlocSk.NB.shG m0) (WlocSk.NB.shH m0)
        (fun i => (WlocSk.NB.continuous_shG m0 i).measurable) (fun i x y h => WlocSk.NB.shG_dep m0 i x y h)
        (WlocSk.NB.continuous_shH m0).measurable
      have key : (lam0.map (fun x => s * x)).map Ψ = lam0.map Ψ := by
        rw [Measure.map_map emb.measurable (measurable_const_mul s), hfun,
          ← Measure.map_map (measurable_lmulM m0) emb.measurable, hmap, hν,
          Measure.map_map (measurable_lmulM m0) hΦe.measurable, hsh,
          ← Measure.map_map hΦe.measurable hmp.measurable, hmp.map_eq]
      rw [← emb.comap_map (lam0.map (fun x => s * x)), key, emb.comap_map]
  have hkc : ∀ᵐ g ∂lam0, kapL ε e f w z g = (Kc T ∘ Ψ) g := by
    filter_upwards [(ae_iff.2 hHaar.2.2.1 : ∀ᵐ g ∂lam0, g ∈ NLoc ε e z)] with g hg
    have hg' : InN ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) (uMat g) := by
      have h1 : g ∈ NLoc ε e (Qm e f w (z0v T z) *ᵥ zBv k r T) := by rw [hNz]; exact hg
      exact h1
    exact kapL_eq hFJ hT g (conj_mem_Nset hFJ hz0 (uMat_mem g) hg')
  have hdet := det_LyM_ne (k := k) (r := r) hT
  set c : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det (LyM (k := k) (r := r) T))⁻¹| with hc
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero hdet))).ne'
  have hcT : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeasK : AEMeasurable (kapL ε e f w z) lam0 :=
    ((Kc_cont T).measurable.comp emb.measurable).aemeasurable.congr (Filter.EventuallyEq.symm hkc)
  have hcomp : Kc T ∘ Φ = LyM (k := k) (r := r) T ∘ Rc := by
    funext t
    funext i
    rw [Function.comp_apply, Function.comp_apply, LyM_apply]
    exact chart_kappa_coordinates T t i
  have hH : Formalism.MainNotions.S.haarLie (Nset k r) 1 = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • ν := by
    rw [hν]
    exact exponential_chart_haar k r
  have hrefN : refNg rfl ε e f w (z0v T z) = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • lam0 := by
    rw [refNg_rfl]
    ext s _
    show (Measure.comap Ψ (Formalism.MainNotions.S.haarLie (Nset k r) 1)) s = _
    rw [emb.comap_apply, hH, Measure.smul_apply, Measure.smul_apply, hlam0, emb.comap_apply]
  have hlamK : lam0.map (kapL ε e f w z) = c • volume := by
    rw [Measure.map_congr hkc, ← Measure.map_map (Kc_cont T).measurable emb.measurable, hmap, hν,
      Measure.map_map (Kc_cont T).measurable hΦe.measurable, hcomp,
      ← Measure.map_map (LyM (k := k) (r := r) T).continuous_of_finiteDimensional.measurable Rc_cont.measurable,
      map_Rc, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, ← hc]
  refine ⟨?_, ?_⟩
  · rw [hrefN]
    exact hmeasK.smul_measure _
  · rw [hrefN, Measure.map_smul, hlamK, smul_smul, hc, det_LyM hT, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [abs_of_pos (by positivity)]
    exact hmeasK

end Formalism.L2.SG.Pf.NcReal.JX
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FrameRow : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u w : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    ∃ L : (LsNc5.CIdx D.R.rS D.R.k → ℝ) →ₗ[ℝ] (LsNc5.CIdx D.R.rS D.R.k → ℝ),
      (∀ s : X.B.I.Ginf, (fun i => LsNc5.kapV X w v s i) = L (fun i => LsNc5.kapV X u v s i)) ∧
      |LinearMap.det L| = (Tw w / Tw u) ^ D.R.rS

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CMeasSbox
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Phi

variable {ι : Type} [Fintype ι] {r k : ℕ}

def Φc (x : ∀ p : CBlk r, CSpc ι k p) (i : ι × LsNc5.CIdx r k) : ℝ :=
  match i with
  | (v, Sum.inl (Sum.inl (p, t))) => LsNc5.reim ((x (Sum.inl (Sum.inl p)) : ι → ℂ) v) t
  | (v, Sum.inl (Sum.inr (b, t))) => LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v (Fin.last k)) t
  | (v, Sum.inr (Sum.inl (b, j, t))) =>
      LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v (Fin.castSucc j)) t
  | (v, Sum.inr (Sum.inr (Sum.inl (p, t)))) => LsNc5.reim ((x (Sum.inr (Sum.inl p)) : ι → ℂ) v) t
  | (v, Sum.inr (Sum.inr (Sum.inr a))) => (x (Sum.inr (Sum.inr a)) : ι → ℝ) v

theorem measurable_Φc : Measurable (Φc (ι := ι) (r := r) (k := k)) := by
  refine Measurable.of_eval fun i => ?_
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inl p) : CBlk r)))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply (Fin.last k)).comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inr b) : CBlk r))))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply (Fin.castSucc j)).comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inl (Sum.inr b) : CBlk r))))
  · exact (reim_cont t).measurable.comp ((measurable_pi_apply v).comp
      (measurable_pi_apply (Sum.inr (Sum.inl p) : CBlk r)))
  · exact (measurable_pi_apply v).comp (measurable_pi_apply (Sum.inr (Sum.inr a) : CBlk r))

def Ψc (y : ι × LsNc5.CIdx r k → ℝ) : ∀ p : CBlk r, CSpc ι k p
  | Sum.inl (Sum.inl p) => fun v => (⟨y (v, Sum.inl (Sum.inl (p, false))), y (v, Sum.inl (Sum.inl (p, true)))⟩ : ℂ)
  | Sum.inl (Sum.inr b) => fun v j =>
      if h : j.val < k then (⟨y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, false))),
        y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, true)))⟩ : ℂ)
      else (⟨y (v, Sum.inl (Sum.inr (b, false))), y (v, Sum.inl (Sum.inr (b, true)))⟩ : ℂ)
  | Sum.inr (Sum.inl p) => fun v =>
      (⟨y (v, Sum.inr (Sum.inr (Sum.inl (p, false)))), y (v, Sum.inr (Sum.inr (Sum.inl (p, true))))⟩ : ℂ)
  | Sum.inr (Sum.inr a) => fun v => y (v, Sum.inr (Sum.inr (Sum.inr a)))

theorem Φc_Ψc (y : ι × LsNc5.CIdx r k → ℝ) : Φc (Ψc y) = y := by
  funext i
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · cases t <;> rfl
  · have hj : ¬ (Fin.last k).val < k := by simp
    cases t <;> simp [Φc, Ψc, hj, LsNc5.reim]
  · have hj : (Fin.castSucc j).val < k := j.isLt
    cases t <;> simp [Φc, Ψc, hj, LsNc5.reim]
  · cases t <;> rfl
  · rfl

theorem Ψc_Φc (x : ∀ p : CBlk r, CSpc ι k p) : Ψc (Φc x) = x := by
  funext p
  rcases p with ((p | b) | (p | a))
  · funext v; apply Complex.ext <;> rfl
  · funext v j
    show (if h : j.val < k then _ else _) = _
    split_ifs with h
    · apply Complex.ext
      · show LsNc5.reim (_ : ℂ) false = _
        simp only [LsNc5.reim, Bool.false_eq_true, if_false]
        congr 2
      · show LsNc5.reim (_ : ℂ) true = _
        simp only [LsNc5.reim, if_true]
        congr 2
    · have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
      subst hj
      apply Complex.ext <;> rfl
  · funext v; apply Complex.ext <;> rfl
  · rfl

theorem measurable_Ψc : Measurable (Ψc (ι := ι) (r := r) (k := k)) := by
  have hC : ∀ f g : (ι × LsNc5.CIdx r k → ℝ) → ℝ, Measurable f → Measurable g →
      Measurable fun y => (⟨f y, g y⟩ : ℂ) := fun f g hf hg =>
    Complex.measurableEquivRealProd.symm.measurable.comp (hf.prodMk hg)
  refine Measurable.of_eval fun p => ?_
  rcases p with ((p | b) | (p | a))
  · exact Measurable.of_eval fun v => hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · refine Measurable.of_eval fun v => Measurable.of_eval fun j => ?_
    show Measurable fun y : ι × LsNc5.CIdx r k → ℝ => (if h : j.val < k then (⟨y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, false))),
        y (v, Sum.inr (Sum.inl (b, ⟨j.val, h⟩, true)))⟩ : ℂ)
      else (⟨y (v, Sum.inl (Sum.inr (b, false))), y (v, Sum.inl (Sum.inr (b, true)))⟩ : ℂ))
    split_ifs with h
    · exact hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
    · exact hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · exact Measurable.of_eval fun v => hC _ _ (measurable_pi_apply _) (measurable_pi_apply _)
  · exact Measurable.of_eval fun v => measurable_pi_apply _

end Phi

section Box

variable {ι : Type} [Fintype ι] {r k : ℕ}

def cRow (b : Fin r) (j : Fin (k + 1)) (t : Bool) : LsNc5.CIdx r k :=
  if h : j.val < k then Sum.inr (Sum.inl (b, ⟨j.val, h⟩, t)) else Sum.inl (Sum.inr (b, t))

def Sbox (s : ι × LsNc5.CIdx r k → Set ℝ) : ∀ p : CBlk r, Set (CSpc ι k p)
  | Sum.inl (Sum.inl p) => Set.univ.pi fun v => {z : ℂ | LsNc5.reim z false ∈ s (v, Sum.inl (Sum.inl (p, false))) ∧
      LsNc5.reim z true ∈ s (v, Sum.inl (Sum.inl (p, true)))}
  | Sum.inl (Sum.inr b) => Set.univ.pi fun v => Set.univ.pi fun j : Fin (k + 1) =>
      {z : ℂ | LsNc5.reim z false ∈ s (v, cRow b j false) ∧ LsNc5.reim z true ∈ s (v, cRow b j true)}
  | Sum.inr (Sum.inl p) => Set.univ.pi fun v => {z : ℂ | LsNc5.reim z false ∈ s (v, Sum.inr (Sum.inr (Sum.inl (p, false)))) ∧
      LsNc5.reim z true ∈ s (v, Sum.inr (Sum.inr (Sum.inl (p, true))))}
  | Sum.inr (Sum.inr a) => Set.univ.pi fun v => s (v, Sum.inr (Sum.inr (Sum.inr a)))

theorem Φc_row (x : ∀ p : CBlk r, CSpc ι k p) (v : ι) (b : Fin r) (j : Fin (k + 1)) (t : Bool) :
    Φc x (v, cRow b j t) = LsNc5.reim ((x (Sum.inl (Sum.inr b)) : ι → Fin (k + 1) → ℂ) v j) t := by
  unfold cRow
  split_ifs with h
  · rfl
  · have hj : j = Fin.last k := Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    subst hj; rfl

theorem pre_box (s : ι × LsNc5.CIdx r k → Set ℝ) :
    Φc ⁻¹' Set.univ.pi s = Set.univ.pi (Sbox (ι := ι) (k := k) s) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  constructor
  · intro h p
    rcases p with ((p | b) | (p | a))
    · intro v _; exact ⟨h (v, Sum.inl (Sum.inl (p, false))), h (v, Sum.inl (Sum.inl (p, true)))⟩
    · intro v _ j _
      refine ⟨?_, ?_⟩
      · have := h (v, cRow b j false); rwa [Φc_row] at this
      · have := h (v, cRow b j true); rwa [Φc_row] at this
    · intro v _; exact ⟨h (v, Sum.inr (Sum.inr (Sum.inl (p, false)))), h (v, Sum.inr (Sum.inr (Sum.inl (p, true))))⟩
    · intro v _; exact h (v, Sum.inr (Sum.inr (Sum.inr a)))
  · intro h i
    rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
    · have := h (Sum.inl (Sum.inl p)) v (Set.mem_univ v); cases t; exacts [this.1, this.2]
    · have := h (Sum.inl (Sum.inr b)) v (Set.mem_univ v) (Fin.last k) (Set.mem_univ _)
      have e : ∀ t, cRow (k := k) b (Fin.last k) t = Sum.inl (Sum.inr (b, t)) := fun t => by simp [cRow]
      have h2 := Φc_row x v b (Fin.last k) t
      rw [e] at h2
      rw [h2]
      cases t
      · have := this.1; rwa [e] at this
      · have := this.2; rwa [e] at this
    · have := h (Sum.inl (Sum.inr b)) v (Set.mem_univ v) (Fin.castSucc j) (Set.mem_univ _)
      have e : ∀ t, cRow (k := k) b (Fin.castSucc j) t = Sum.inr (Sum.inl (b, j, t)) := fun t => by
        simp [cRow]
      have h2 := Φc_row x v b (Fin.castSucc j) t
      rw [e] at h2
      rw [h2]
      cases t
      · have := this.1; rwa [e] at this
      · have := this.2; rwa [e] at this
    · have := h (Sum.inr (Sum.inl p)) v (Set.mem_univ v); cases t; exacts [this.1, this.2]
    · exact h (Sum.inr (Sum.inr a)) v (Set.mem_univ v)

theorem cMeas_Sbox (s : ι × LsNc5.CIdx r k → Set ℝ) (hs : ∀ i, MeasurableSet (s i)) (p : CBlk r) :
    cMeas ι k p (Sbox s p) =
      match p with
      | Sum.inl (Sum.inl p) => ∏ v, volume (s (v, Sum.inl (Sum.inl (p, false)))) * volume (s (v, Sum.inl (Sum.inl (p, true))))
      | Sum.inl (Sum.inr b) => ∏ v, ∏ j : Fin (k + 1), volume (s (v, cRow b j false)) * volume (s (v, cRow b j true))
      | Sum.inr (Sum.inl p) => ∏ v, volume (s (v, Sum.inr (Sum.inr (Sum.inl (p, false))))) *
          volume (s (v, Sum.inr (Sum.inr (Sum.inl (p, true)))))
      | Sum.inr (Sum.inr a) => ∏ v, volume (s (v, Sum.inr (Sum.inr (Sum.inr a)))) := by
  rcases p with ((p | b) | (p | a))
  · show (volume : Measure (ι → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun v _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → Fin (k + 1) → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun j _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → ℂ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]
    exact Finset.prod_congr rfl fun v _ => volume_reim _ _ (hs _) (hs _)
  · show (volume : Measure (ι → ℝ)) (Set.univ.pi _) = _
    rw [volume_pi_pi]

theorem map_Φc : (Measure.pi (cMeas ι k (r := r))).map Φc = volume := by
  refine (Measure.pi_eq (μ := fun _ : ι × LsNc5.CIdx r k => (volume : Measure ℝ))
    (μ' := (Measure.pi (cMeas ι k (r := r))).map Φc) fun s hs => ?_).symm
  rw [Measure.map_apply measurable_Φc (MeasurableSet.univ_pi hs), pre_box, Measure.pi_pi]
  simp_rw [cMeas_Sbox s hs]
  rw [Fintype.prod_prod_type]
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type, Fintype.prod_bool, Fin.prod_univ_castSucc,
    Finset.prod_mul_distrib]
  have e1 : ∀ (b : Fin r) (t : Bool), cRow (k := k) b (Fin.last k) t = Sum.inl (Sum.inr (b, t)) := fun b t => by
    simp [cRow]
  have e2 : ∀ (b : Fin r) (j : Fin k) (t : Bool), cRow (k := k) b (Fin.castSucc j) t = Sum.inr (Sum.inl (b, j, t)) :=
    fun b j t => by simp [cRow]
  simp only [e1, e2]
  have swap : ∀ {β : Type} [Fintype β] (f : ι → β → ℝ≥0∞), ∏ v, ∏ b, f v b = ∏ b, ∏ v, f v b :=
    fun f => Finset.prod_comm
  simp only [swap]
  ring

end Box

theorem kap_eq_Φc {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) :
    LsNc5.kap X u s = Φc (blk X u s) := by
  funext i
  rcases i with ⟨v, ((⟨p, t⟩ | ⟨b, t⟩) | (⟨b, j, t⟩ | (⟨p, t⟩ | a)))⟩
  · rfl
  · show LsNc5.reim (LsNc5.yVec X u v s b) t = LsNc5.reim (blk X u s (Sum.inl (Sum.inr b)) v (Fin.last D.R.k)) t
    simp [blk]
  · show LsNc5.reim (LsNc5.phiMat X u v s b j) t =
      LsNc5.reim (blk X u s (Sum.inl (Sum.inr b)) v (Fin.castSucc j)) t
    simp [blk]
  · rfl
  · rfl

end Formalism.L2.SG.Pf.NcReal.JX
end
end
