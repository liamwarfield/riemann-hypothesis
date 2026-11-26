module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingClassGroupDescentsDifferByPowerPrimeToL
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingClassGroupDescentsDifferByPowerPrimeToL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem pulls_eq_zpow : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b b' : Bool) (v v' : D.what₂.places.Pl) (ρ : Reading i k b v) (ρ' : Reading i k b' v') (Q : Finset (PlE D.host)) (ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l i ^ k)) → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → ρ.Pulls ψ ψ₀ → ρ'.Pulls ψ' ψ₀ → ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) ∧ ψ' = ψ ^ a := by
  intro D i k b b' v v' ρ ρ' Q ψ ψ' ψ₀ ⟨z, hz⟩ hpow hρ hρ'
  have hl := (D.ntw.lPrime i).out
  let ι : D.ntw.Ok i k →+* FractionRing ρ.Oe := (algebraMap ρ.Oe (FractionRing ρ.Oe)).comp (algebraMap _ ρ.Oe)
  let ι' : D.ntw.Ok i k →+* FractionRing ρ'.Oe := (algebraMap ρ'.Oe (FractionRing ρ'.Oe)).comp (algebraMap _ ρ'.Oe)
  have hι : Function.Injective ι := (IsFractionRing.injective ρ.Oe (FractionRing ρ.Oe)).comp ρ.inj
  have hι' : Function.Injective ι' := (IsFractionRing.injective ρ'.Oe (FractionRing ρ'.Oe)).comp ρ'.inj
  have e1 : ∀ g, ι ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) = ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
    fun g => (hρ g).symm
  have e1' : ∀ g, ι' ((ψ' (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) = ρ'.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
    fun g => (hρ' g).symm
  have hp : ∀ g, ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) ^ (D.ntw.l i ^ k) = 1 := fun g => by
    rw [← Units.val_pow_eq_pow_val, hpow g, Units.val_one]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, by simp, ?_⟩
    ext x
    obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q x
    have h1 : ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = 1 := by simpa using hp g
    have h2 := e1 g
    have h2' := e1' g
    rw [h1, map_one, ← map_one ι] at h2
    rw [h1, map_one, ← map_one ι'] at h2'
    rw [hι' h2', zpow_one, hι h2]
  · have hN : 0 < D.ntw.l i ^ k := pow_pos hl.pos k
    haveI : NeZero (D.ntw.l i ^ k) := ⟨hN.ne'⟩
    have hζ := D.ntw.zk_prim i k
    have he : IsPrimitiveRoot (ρ.emb z) (D.ntw.l i ^ k) := hz.map_of_injective ρ.emb.injective
    have he' : IsPrimitiveRoot (ρ'.emb z) (D.ntw.l i ^ k) := hz.map_of_injective ρ'.emb.injective
    have hζe : IsPrimitiveRoot (ι (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k) := hζ.map_of_injective hι
    have hζe' : IsPrimitiveRoot (ι' (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k) := hζ.map_of_injective hι'
    obtain ⟨c, -, hc⟩ := he.eq_pow_of_pow_eq_one hζe.pow_eq_one
    obtain ⟨a, -, ha⟩ := hζe'.eq_pow_of_pow_eq_one he'.pow_eq_one
    have hcc : c.Coprime (D.ntw.l i ^ k) := (he.pow_iff_coprime hN c).1 (hc ▸ hζe)
    have hac : a.Coprime (D.ntw.l i ^ k) := (hζe'.pow_iff_coprime hN a).1 (ha ▸ he')
    refine ⟨((c * a : ℕ) : ℤ), ?_, ?_⟩
    · rw [Int.natAbs_natCast]
      exact (Nat.Coprime.mul_left hcc hac).coprime_dvd_right (dvd_pow_self _ hk.ne')
    · ext x
      obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q x
      obtain ⟨n, -, hn⟩ := hz.eq_pow_of_pow_eq_one (hp g)
      have k1 : ι ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) ^ (c * a) =
          ι ((D.ntw.zk i k : D.ntw.Ok i k) ^ (n * a)) := by
        rw [e1 g, ← hn, map_pow, map_pow, ← hc, ← pow_mul, ← pow_mul]
        ring_nf
      have k2 : ι' ((ψ' (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) =
          ι' ((D.ntw.zk i k : D.ntw.Ok i k) ^ (n * a)) := by
        rw [e1' g, ← hn, map_pow, map_pow, ← ha, ← pow_mul]
        ring_nf
      rw [← map_pow] at k1
      rw [hι' k2, zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hι k1]

end GlobalTheory.LevCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingClassGroupDescentsDifferByPowerPrimeToLStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringClassGroup_descents_differ_by_power_prime_to_l : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b b' : Bool) (v v' : D.what₂.places.Pl) (ρ : Reading i k b v) (ρ' : Reading i k b' v') (Q : Finset (PlE D.host)) (ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l i ^ k)) → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → ρ.Pulls ψ ψ₀ → ρ'.Pulls ψ' ψ₀ → ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) ∧ ψ' = ψ ^ a := by
  first | exact @GlobalTheory.LevCmp.pulls_eq_zpow | exact GlobalTheory.LevCmp.pulls_eq_zpow | (intros; apply GlobalTheory.LevCmp.pulls_eq_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProductLevelDefiniteFormsRealisationAtTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProductLevelDefiniteFormsRealisationAtTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevProd

open GlobalTheory.MtInProd
open _root_.Formalism.L2.NX (locM InLevG InParah inParah_one)
open Classical

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eA (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    s.proj (eA L v) = if s.v = v then 1 else 0 := by
  show s.i 1 * (idemF (L := L) v) s.v = _
  rw [map_one, one_mul, idemF_apply]

theorem locM_cut (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n) :
    locM s (cutGA (eA_mul v) (conj_eA v) κ) = if s.v = v then locM s κ else 1 := by
  show ((cutGA (eA_mul v) (conj_eA v) κ).1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj = _
  rw [cutGA_val, map_cutMat, proj_eA]
  split_ifs
  · rw [cutMat_one_left]; rfl
  · rw [cutMat_zero_left]

theorem inLevG_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) :
    InLevG v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) := by
  refine ⟨inParah_one v r, fun a b _ _ => ⟨fun hba => ?_, fun hab => ?_⟩⟩
  · have h : a ≠ b := fun e => by subst e; exact lt_irrefl _ hba
    rw [Matrix.one_apply_ne h, map_zero]
    exact WithZero.zero_lt_coe _
  · subst hab
    rw [Matrix.one_apply_eq, sub_self, map_zero]
    exact WithZero.zero_lt_coe _

end Gen

theorem main : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m), NG.IsProdLevel (cell X b hA j).J := by
  intro D X i b k Q ψ hA j κ hκ v
  obtain ⟨hU, hG, hQ, hD⟩ := ((cell X b hA j).J_mem κ).1 hκ
  refine ⟨cutGA (eA_mul v) (conj_eA v) κ, ((cell X b hA j).J_mem _).2 ⟨cutGA_mem_Umax _ _ (eA_mem v) hU, fun kv => ?_,
    fun P hP => ?_, fun P hP => ?_⟩, triv_cut_eA v κ, cut_eA_at v κ⟩
  · rw [locM_cut]; split_ifs
    · exact hG kv
    · exact inLevG_one _ _
  · rw [locM_cut]; split_ifs
    · exact hQ P hP
    · exact inParah_one _ _
  · rw [locM_cut]; split_ifs
    · exact hD P hP
    · exact inParah_one _ _

end GlobalTheory.LevProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProductLevelDefiniteFormsRealisationAtTwistStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProductLevel_definiteFormsRealisationAtTwist : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m), NG.IsProdLevel (cell X b hA j).J := by
  first | exact @GlobalTheory.LevProd.main | exact GlobalTheory.LevProd.main | (intros; apply GlobalTheory.LevProd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisCharacterOfFiniteOrderHeckeCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisCharacterOfFiniteOrderHeckeCharacter
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem galOf_of_orderDvd : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (χ : HChar D.host.E) (n : ℕ), 0 < n → χ.OrderDvd n → (∃ z : D.what₂.LL, IsPrimitiveRoot z n) → ∃ ψ₀, GalOf D χ ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1 := by
  intro hGAR D χ n hn hχ hz
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  have h1 : ∀ x, χ.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) hχ
  have hko : IsOpen (χ.1.ker : Set (Ideles D.host.E)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hn h1
  have hkc : IsClosed (χ.1.ker : Set (Ideles D.host.E)) := Subgroup.isClosed_of_isOpen _ hko
  have hle : art.ker ≤ χ.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc
    · rintro _ ⟨k, rfl⟩
      exact χ.2.2 k
    · rw [GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]
      intro y hy
      have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) :=
        Continuous.units_map _ (continuous_id.prodMk continuous_const)
      have hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) χ.1.ker : Subgroup _) : Set (InfiniteAdeleRing D.host.E)ˣ) :=
        ⟨hkc.preimage hinl, hko.preimage hinl⟩
      exact hcl.connectedComponent_subset (Subgroup.one_mem _) hy
  let e := QuotientGroup.quotientKerEquivOfSurjective art ha.quot.surjective
  let c : Gab D.host.E D.nd.Om →* ℂˣ := (QuotientGroup.lift art.ker χ.1 hle).comp e.symm.toMonoidHom
  have hc : ∀ x, c (art x) = χ.1 x := fun x => by
    show QuotientGroup.lift art.ker χ.1 hle (e.symm (art x)) = χ.1 x
    have : e.symm (art x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
    rw [this]; rfl
  have hcc : Continuous c := by
    rw [ha.quot.isQuotientMap.continuous_iff]
    have : (c ∘ art) = χ.1 := funext hc
    rw [this]; exact χ.2.1
  let r : G D.host.E D.nd.Om →* ℂˣ := c.comp (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om)
  have hrc : Continuous r := hcc.comp continuous_quot_mk
  have hrn : ∀ g, r g ^ n = 1 := fun g => by
    obtain ⟨x, hx⟩ := ha.quot.surjective (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om g)
    show c _ ^ n = 1
    rw [← hx, hc, h1]
  have hro : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow r hrc hn hrn
  obtain ⟨z, hz⟩ := hz
  obtain ⟨ψ, hψ⟩ := GlobalTheory.TwistChoice.exists_char_descent D.what₂.embLL hn hz r hrn
  have hψr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ = r := MonoidHom.ext fun g => Units.ext (hψ g)
  have hker : ψ.ker = r.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    rw [← hψr, MonoidHom.comp_apply]
    constructor
    · intro h; rw [h, map_one]
    · intro h
      apply Units.ext
      apply D.what₂.embLL.injective
      have := congrArg Units.val h
      simpa using this
  refine ⟨ψ, ⟨by rw [hker]; exact hro, art, ha, ?_⟩, fun g => ?_⟩
  · rw [hψr]
    intro x σ hσ
    show χ.1 x = c (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ)
    rw [← hσ, hc]
  · apply Units.ext
    apply D.what₂.embLL.injective
    have := congrArg Units.val (hrn g)
    rw [← hψr] at this
    simpa using this

end GlobalTheory.LevCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisCharacterOfFiniteOrderHeckeCharacterStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisCharacter_of_finiteOrder_heckeCharacter : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (χ : HChar D.host.E) (n : ℕ), 0 < n → χ.OrderDvd n → (∃ z : D.what₂.LL, IsPrimitiveRoot z n) → ∃ ψ₀, GalOf D χ ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1 := by
  first | exact @GlobalTheory.LevCmp.galOf_of_orderDvd | exact GlobalTheory.LevCmp.galOf_of_orderDvd | (intros; apply GlobalTheory.LevCmp.galOf_of_orderDvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexEmbeddingReadingFractionRingOverCoe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosedContinuumRingEquivComplexExtending
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem algClosed_continuum_ringEquiv_complex_extending :
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C], Cardinal.mk C = Cardinal.continuum →
      ∀ (K : Type) [Field K] [NumberField K] (i : K →+* C) (s : K →+* ℂ),
        ∃ e : C ≃+* ℂ, ∀ x, e (i x) = s x := by
  intro C _ _ _ hC K _ _ i s
  obtain ⟨e₀⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := C) (L := ℂ)
    (by rw [hC]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [hC, Cardinal.mk_complex]))
  haveI : Countable K :=
    Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.symm.toEquiv
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq K (e₀.toRingHom.comp i) s
  exact ⟨e₀.trans τ, fun x => hτ x⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexEmbeddingReadingFractionRingOverCoe
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ReadingEmb

theorem exists_ringHom_complex_extending (A : Type) [Field A] (hA : Cardinal.mk A ≤ Cardinal.continuum)
    (K : Type) [Field K] [NumberField K] (i : K →+* A) (s : K →+* ℂ) :
    ∃ ι : A →+* ℂ, ∀ x, ι (i x) = s x := by
  haveI : CharZero A := (RingHom.charZero_iff i.injective).1 inferInstance
  let B := FractionRing (MvPolynomial ℝ A)
  have hB : Cardinal.mk B = Cardinal.continuum := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hA,
      max_eq_left Cardinal.aleph0_le_continuum]
  let C := AlgebraicClosure B
  have hC : Cardinal.mk C = Cardinal.continuum := by
    refine le_antisymm ((Algebra.IsAlgebraic.cardinalMk_le_max B C).trans
      (max_le hB.le Cardinal.aleph0_le_continuum)) ?_
    rw [← hB]
    exact Cardinal.mk_le_of_injective (algebraMap B C).injective
  let j : A →+* C := (algebraMap B C).comp ((algebraMap (MvPolynomial ℝ A) B).comp MvPolynomial.C)
  haveI : CharZero C := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e, he⟩ := GlobalTheory.algClosed_continuum_ringEquiv_complex_extending C hC K (j.comp i) s
  exact ⟨e.toRingHom.comp j, fun x => he x⟩

theorem mk_le_of_finite (R S : Type) [CommRing R] [AddCommGroup S] [Module R S] [Module.Finite R S]
    (h : Cardinal.mk R ≤ Cardinal.continuum) : Cardinal.mk S ≤ Cardinal.continuum := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R S
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_fin]
  calc Cardinal.mk R ^ (n : Cardinal) ≤ Cardinal.continuum ^ (n : Cardinal) := Cardinal.power_le_power_right h
    _ ≤ Cardinal.continuum ^ Cardinal.aleph0 :=
        Cardinal.power_le_power_left Cardinal.continuum_ne_zero (Cardinal.natCast_le_aleph0)
    _ = Cardinal.continuum := Cardinal.continuum_power_aleph0

theorem exists_complex_emb : ∀ (D : D7) (F : TwFrameC D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), ∃ ι : FractionRing ρ.Oe →+* ℂ, ∀ x, ι (ρ.emb x) = D.what₂.embLL x := by
  intro D F i k b v ρ
  haveI := D.ntw.lPrime i
  have h1 : Cardinal.mk (D.ntw.Ok i k) ≤ Cardinal.continuum := by
    have hinj : Function.Injective (fun x : D.ntw.Ok i k => ((F.eOk i k x : _) : ℂ_[D.ntw.l i])) :=
      Subtype.val_injective.comp (F.eOk i k).injective
    refine (Cardinal.mk_le_of_injective hinj).trans ?_
    rw [(GlobalTheory.PadicCard.card_padicAlgCl_padicComplex (D.ntw.l i)).2, Cardinal.mk_complex]
  haveI := ρ.fin
  have h2 : Cardinal.mk ρ.Oe ≤ Cardinal.continuum := mk_le_of_finite (D.ntw.Ok i k) ρ.Oe h1
  exact exists_ringHom_complex_extending (FractionRing ρ.Oe) (by rw [Cardinal.mk_fractionRing]; exact h2)
    D.what₂.LL ρ.emb D.what₂.embLL

end GlobalTheory.ReadingEmb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexEmbeddingReadingFractionRingOverCoeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexEmbedding_readingFractionRing_over_coeffField : ∀ (D : D7) (F : TwFrameC D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), ∃ ι : FractionRing ρ.Oe →+* ℂ, ∀ x, ι (ρ.emb x) = D.what₂.embLL x := by
  first | exact @GlobalTheory.ReadingEmb.exists_complex_emb | exact GlobalTheory.ReadingEmb.exists_complex_emb | (intros; apply GlobalTheory.ReadingEmb.exists_complex_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperParahoricLowerDetUnitAndSuperdiagIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperParahoricLowerDetUnitAndSuperdiagIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ParaUnit

theorem val_det_block {K Γ ι : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] [Fintype ι] [DecidableEq ι]
    (v : Valuation K Γ) (p : ι → Prop) [DecidablePred p] (A B : Matrix ι ι K)
    (hA : ∀ a b, v (A a b) ≤ 1) (hB : ∀ a b, v (B a b) ≤ 1) (hAB : A * B = 1)
    (hlow : ∀ a b, p a → ¬ p b → v (A a b) < 1) :
    v (Matrix.of fun a b : {x // p x} => A a.1 b.1).det = 1 := by
  let O := v.valuationSubring
  let A' : Matrix ι ι O := Matrix.of fun a b => ⟨A a b, hA a b⟩
  let B' : Matrix ι ι O := Matrix.of fun a b => ⟨B a b, hB a b⟩
  have hAB' : A' * B' = 1 := by
    ext a b
    have := congrFun (congrFun hAB a) b
    rw [Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.one_apply] at this ⊢
    rw [AddSubmonoidClass.coe_finsetSum, apply_ite (fun x : O => (x : K))]
    simpa [A', B'] using this
  let f := IsLocalRing.residue O
  have hf : ∀ a b, p a → ¬ p b → f (A' a b) = 0 := by
    intro a b ha hb
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact hlow a b ha hb
  let A₁ : Matrix {x // p x} {x // p x} O := Matrix.of fun a b => A' a.1 b.1
  let B₁ : Matrix {x // p x} {x // p x} O := Matrix.of fun a b => B' a.1 b.1
  have h1 : f.mapMatrix A₁ * f.mapMatrix B₁ = 1 := by
    ext a b
    have h := congrArg f (congrFun (congrFun hAB' a.1) b.1)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, ← Fintype.sum_subtype_add_sum_subtype p] at h
    rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {x // ¬ p x}))
      (fun c _ => by rw [map_mul, hf a.1 c.1 a.2 c.2, zero_mul]), add_zero] at h
    rw [Matrix.mul_apply]
    simp only [map_mul] at h
    refine Eq.trans h ?_
    simp only [Matrix.one_apply, Subtype.ext_iff]
    split_ifs <;> simp
  have h2 : f A₁.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, ← RingHom.map_det, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h3 : ((A₁.det : O) : K) = (Matrix.of fun a b : {x // p x} => A a.1 b.1).det := by
    have := RingHom.map_det O.subtype A₁
    exact this
  rw [← h3]
  refine le_antisymm A₁.det.2 (not_lt.1 fun hlt => h2 ?_)
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  exact hlt

theorem detDD_unit_supDiag_int : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), NG.ParaRT s r h → Valued.v (NG.detDD s r h) = 1 ∧ Valued.v (NG.supDiag s r h) ≤ 1 := by
  intro L _ _ _ n r s h hp
  have key : ∀ g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring →
      ∀ a b, Valued.v (g.val a b) ≤ 1 := by
    rintro g ⟨x, rfl⟩ a b
    exact (x.val a b).2
  have hA := key h hp.1
  have hB := key h⁻¹ (inv_mem hp.1)
  refine ⟨?_, ?_⟩
  · exact val_det_block Valued.v (fun x : Fin n => r ≤ x.val) h.val (h⁻¹).val hA hB (by simp)
      (fun a b ha hb => hp.2 a b ha (not_le.1 hb))
  · unfold NG.supDiag
    refine Valuation.map_sum_le _ fun a _ => Valuation.map_sum_le _ fun b _ => ?_
    split_ifs
    · exact hA a b
    · simp

end GlobalTheory.ParaUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperParahoricLowerDetUnitAndSuperdiagIntegralStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperParahoric_lowerDet_unit_and_superdiag_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), NG.ParaRT s r h → Valued.v (NG.detDD s r h) = 1 ∧ Valued.v (NG.supDiag s r h) ≤ 1 := by
  first | exact @GlobalTheory.ParaUnit.detDD_unit_supDiag_int | exact GlobalTheory.ParaUnit.detDD_unit_supDiag_int | (intros; apply GlobalTheory.ParaUnit.detDD_unit_supDiag_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpectedShapeLevelIntegralAndUnipotentAtTypePlac
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpectedShapeLevelIntegralAndUnipotentAtTypePlac
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevShapeBound

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eq_of_compAt (s : SplitPlace L) {x y : AL L}
    (h : compAt L s.v x = compAt L s.v y) : s.proj x = s.proj y := by
  have key : ∀ z : AL L, s.proj z =
      (Algebra.TensorProduct.lift s.i (AlgHom.id _ (s.v.adicCompletion (maximalRealSubfield L)))
        (fun _ _ => Commute.all _ _)) (compAt L s.v z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]
  rw [key, key, h]

theorem loc_eq_of_comp (s : SplitPlace L) {x y : GAf L n}
    (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v)) :
    s.loc n x = s.loc n y := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at hij
  exact proj_eq_of_compAt s hij

end Gen

theorem bound : ∀ (D : D7) (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)), GPlaces D → GrpShape D η J → ∀ κ ∈ J, κ ∈ Umax D.host.E D.R.nV ∧ ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → NG.UniRT s D.R.r (s.loc _ κ) := by
  intro D η J hG hS κ hκ
  obtain ⟨hprod, hpara, huni, hhyp⟩ := hS

  have hloc : ∀ w, ∃ κ' ∈ J, κ' ∈ Umax D.host.E D.R.nV ∧
      (κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) =
        (κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) := by
    intro w
    obtain ⟨κ', hκ', htr, heq⟩ := hprod κ hκ w
    refine ⟨κ', hκ', ?_, heq⟩
    by_cases hg : w ∈ gPl D
    · obtain ⟨k, v, s, hsv, hsw⟩ := hG.2.1 w hg
      subst hsv
      have hu := (huni k v s hsw κ' htr).1 hκ'
      exact (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hu.1.1
    · by_cases hq : w ∈ qPl D η
      · obtain ⟨s, hsv, hs⟩ := hpara w hq
        subst hsv
        have hp := (hs κ' htr).1 hκ'
        exact (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hp.1
      · refine (hhyp κ' ?_).1 hκ'
        intro u hu
        apply htr u
        rintro rfl
        simp only [Set.mem_compl_iff, not_not, Set.mem_union] at hu
        rcases hu with h | h
        · exact hg h
        · exact hq h
  refine ⟨?_, ?_⟩
  · intro i j
    apply GlobalTheory.FormInner.mem_ALint_of_comp
    intro w
    obtain ⟨κ', -, hU, heq⟩ := hloc w
    refine ⟨(κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)) i j, hU i j, ?_⟩
    have := congrFun (congrFun heq i) j
    simpa only [Matrix.map_apply] using this
  · intro k v s hsw
    obtain ⟨κ', hκ', htr, heq⟩ := hprod κ hκ s.v
    have hu := (huni k v s hsw κ' htr).1 hκ'
    rwa [loc_eq_of_comp s heq] at hu

end GlobalTheory.LevShapeBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpectedShapeLevelIntegralAndUnipotentAtTypePlacStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expectedShapeLevel_integral_and_unipotent_at_typePlaces : ∀ (D : D7) (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)), GPlaces D → GrpShape D η J → ∀ κ ∈ J, κ ∈ Umax D.host.E D.R.nV ∧ ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → NG.UniRT s D.R.r (s.loc _ κ) := by
  first | exact @GlobalTheory.LevShapeBound.bound | exact GlobalTheory.LevShapeBound.bound | (intros; apply GlobalTheory.LevShapeBound.bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAlgebraicModularFormOfTrivialStabili
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAlgebraicModularFormOfTrivialStabili
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ClassForm

theorem double_coset_unique {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {J : Subgroup (GAf L n)} {g : GAf L n}
    (hg : ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1)
    {γ γ' : GQ L n} {κ κ' : J} (h : (γ : GAf L n) * g * κ = (γ' : GAf L n) * g * κ') : γ = γ' ∧ κ = κ' := by
  have key : g⁻¹ * ((γ' : GAf L n)⁻¹ * γ) * g = (κ' : GAf L n) * (κ : GAf L n)⁻¹ := by
    calc g⁻¹ * ((γ' : GAf L n)⁻¹ * γ) * g
        = g⁻¹ * (γ' : GAf L n)⁻¹ * ((γ : GAf L n) * g * κ) * (κ : GAf L n)⁻¹ := by group
      _ = g⁻¹ * (γ' : GAf L n)⁻¹ * ((γ' : GAf L n) * g * κ') * (κ : GAf L n)⁻¹ := by rw [h]
      _ = (κ' : GAf L n) * (κ : GAf L n)⁻¹ := by group
  have hmem : (γ' : GAf L n)⁻¹ * γ ∈ GQ L n := (GQ L n).mul_mem ((GQ L n).inv_mem γ'.2) γ.2
  have h1 := hg _ hmem (key ▸ J.mul_mem κ'.2 (J.inv_mem κ.2))
  have hγ : (γ : GAf L n) = γ' := by
    rw [inv_mul_eq_one] at h1; exact h1.symm
  refine ⟨Subtype.ext hγ, Subtype.ext ?_⟩
  rw [hγ, mul_assoc, mul_assoc] at h
  exact (mul_left_cancel (mul_left_cancel h))


open Classical in
noncomputable def cosetForm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (w : W) (x : GAf L n) : W :=
  if h : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2 then ((χ h.choose.2 : Kˣ) : K) • ρ h.choose.1 w else 0

theorem cosetForm_apply {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (hg : ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) (w : W) (γ : GQ L n) (κ : J) :
    cosetForm ρ J χ g w ((γ : GAf L n) * g * κ) = ((χ κ : Kˣ) : K) • ρ γ w := by
  have hex : ∃ p : GQ L n × J, (γ : GAf L n) * g * κ = (p.1 : GAf L n) * g * p.2 := ⟨(γ, κ), rfl⟩
  unfold cosetForm
  rw [dite_eq_left hex]
  obtain ⟨h1, h2⟩ := double_coset_unique hg hex.choose_spec
  rw [← h1, ← h2]

theorem cosetForm_not {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (w : W) (x : GAf L n) (hx : ¬ ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2) :
    cosetForm ρ J χ g w x = 0 := by
  unfold cosetForm; rw [dite_eq_right hx]

theorem exists_form_of_trivial_stabiliser : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] [Nontrivial W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ) (g : GAf L n), (∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) → ∃ f ∈ NX.TypeSpF L n K ρ J χ, f ≠ 0 := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ g hg
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  refine ⟨cosetForm ρ J χ g w, ⟨fun δ x => ?_, fun μ x => ?_⟩, fun h0 => hw ?_⟩
  · by_cases hx : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2
    · obtain ⟨⟨γ, κ⟩, rfl⟩ := hx
      have e : (δ : GAf L n) * ((γ : GAf L n) * g * κ) = ((δ * γ : GQ L n) : GAf L n) * g * κ := by
        simp [mul_assoc]
      rw [e, cosetForm_apply ρ J χ g hg, cosetForm_apply ρ J χ g hg, map_smul, map_mul, Module.End.mul_apply]
    · have hx' : ¬ ∃ p : GQ L n × J, (δ : GAf L n) * x = (p.1 : GAf L n) * g * p.2 := by
        rintro ⟨⟨γ, κ⟩, hp⟩
        refine hx ⟨(δ⁻¹ * γ, κ), ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] at hp ⊢
        rw [← hp]; group
      rw [cosetForm_not ρ J χ g w _ hx, cosetForm_not ρ J χ g w _ hx', map_zero]
  · by_cases hx : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2
    · obtain ⟨⟨γ, κ⟩, rfl⟩ := hx
      have e : (γ : GAf L n) * g * κ * μ = (γ : GAf L n) * g * ((κ * μ : J) : GAf L n) := by
        simp [mul_assoc]
      rw [e, cosetForm_apply ρ J χ g hg, cosetForm_apply ρ J χ g hg, map_mul, Units.val_mul, mul_comm, mul_smul]
    · have hx' : ¬ ∃ p : GQ L n × J, x * μ = (p.1 : GAf L n) * g * p.2 := by
        rintro ⟨⟨γ, κ⟩, hp⟩
        refine hx ⟨(γ, κ * μ⁻¹), ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hp ⊢
        rw [← mul_assoc, ← hp]; group
      rw [cosetForm_not ρ J χ g w _ hx, cosetForm_not ρ J χ g w _ hx', smul_zero]
  · have := congrFun h0 g
    have e := cosetForm_apply ρ J χ g hg w 1 1
    simp only [OneMemClass.coe_one, one_mul, mul_one, map_one, Units.val_one, one_smul] at e
    rw [e, Module.End.one_apply] at this
    simpa using this

end GlobalTheory.ClassForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAlgebraicModularFormOfTrivialStabiliStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_algebraicModularForm_of_trivial_stabiliser : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] [Nontrivial W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ) (g : GAf L n), (∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) → ∃ f ∈ NX.TypeSpF L n K ρ J χ, f ≠ 0 := by
  first | exact @GlobalTheory.ClassForm.exists_form_of_trivial_stabiliser | exact GlobalTheory.ClassForm.exists_form_of_trivial_stabiliser | (intros; apply GlobalTheory.ClassForm.exists_form_of_trivial_stabiliser <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassGroupDescentOfCoeffFieldTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassGroupDescentOfCoeffFieldTwist
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TwistDescent

variable {D : D7} {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl}

abbrev rd (ρ : Reading i k b v) : D.ntw.Ok i k →+* FractionRing ρ.Oe :=
  (algebraMap ρ.Oe (FractionRing ρ.Oe)).comp (algebraMap (D.ntw.Ok i k) ρ.Oe)

theorem rd_injective (ρ : Reading i k b v) : Function.Injective (rd ρ) :=
  (IsFractionRing.injective ρ.Oe (FractionRing ρ.Oe)).comp ρ.inj

theorem eq_iff_of_reads {ρ : Reading i k b v} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (g g' : G D.host.E D.nd.Om) : χ g = χ g' ↔ ψ₀ g = ψ₀ g' := by
  constructor
  · intro he
    apply Units.ext
    apply ρ.emb.injective
    rw [h g, h g', he]
  · intro he
    apply Units.ext
    apply rd_injective ρ
    rw [← h g, ← h g', he]

theorem one_iff_of_reads {ρ : Reading i k b v} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (g : G D.host.E D.nd.Om) : χ g = 1 ↔ ψ₀ g = 1 := by
  simpa using eq_iff_of_reads h g 1

theorem twOK_of_reads {ρ : Reading i k b v} {Q : Finset (PlE D.host)} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (hs : ∀ u ∈ Q, IsSplitPl D.host u) (hd : Disjoint Q (D.ntw.S0 i))
    (ho : IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om))) (ha : AntiHom D.ntw.cc ψ₀)
    (hp : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) (hr : RamExactly ψ₀ (↑Q : Set (PlE D.host)))
    (ht : BlochKatoReduction.Gen.TrivAbove ψ₀ (D.ntw.l i)) : IntegralHeckeForms.TwOK i k Q χ := by
  have hker : (χ.ker : Set (G D.host.E D.nd.Om)) = ψ₀.ker := Set.ext fun g => by
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    exact one_iff_of_reads h g
  refine ⟨hs, hd, hker ▸ ho, fun g g' hg => ?_, fun g => ?_, fun w A hA => ?_, fun w hw A hA σ hσ => ?_⟩
  · rw [← map_inv, eq_iff_of_reads h, map_inv]
    exact ha g g' hg
  · have h1 : χ g ^ (D.ntw.l i ^ k) = 1 := by
      rw [← map_pow, one_iff_of_reads h, map_pow]
      exact hp g
    have h2 : ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) ^ (D.ntw.l i ^ k) = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨a, -, h3⟩ := (D.ntw.zk_prim i k).eq_pow_of_pow_eq_one h2
    refine Subgroup.mem_zpowers_iff.2 ⟨(a : ℤ), ?_⟩
    rw [zpow_natCast]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h3)
  · rw [← hr w A hA]
    simp only [ne_eq, one_iff_of_reads h]
  · exact (one_iff_of_reads h σ).2 (ht w hw A hA σ hσ)

theorem exists_reads {ρ : Reading i k b v} (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)
    (hp : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) :
    ∃ χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ, (∀ g, χ g ∈ Subgroup.zpowers (D.ntw.zk i k)) ∧
      ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) := by
  have hz : IsPrimitiveRoot (rd ρ (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k) :=
    (D.ntw.zk_prim i k).map_of_injective (rd_injective ρ)
  have hx : ∀ g, ∃ a : ℕ, rd ρ (((D.ntw.zk i k) ^ a : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) =
      ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) := fun g => by
    have h1 : (ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL)) ^ (D.ntw.l i ^ k) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hp g, Units.val_one, map_one]
    obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one h1
    exact ⟨a, by rw [Units.val_pow_eq_pow_val, map_pow]; exact ha⟩
  choose a ha using hx
  let χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ := MonoidHom.mk' (fun g => D.ntw.zk i k ^ a g) fun g g' => by
    apply Units.ext
    apply rd_injective ρ
    rw [ha (g * g'), map_mul ψ₀, Units.val_mul, map_mul ρ.emb, Units.val_mul, map_mul (rd ρ), ha, ha]
  refine ⟨χ, fun g => ⟨(a g : ℤ), by simp [χ]⟩, fun g => (ha g).symm⟩

theorem exists_pulls_twOK : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v) (Q : Finset (PlE D.host)) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∀ u ∈ Q, IsSplitPl D.host u) → Disjoint Q (D.ntw.S0 i) → IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) → AntiHom D.ntw.cc ψ₀ → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → RamExactly ψ₀ (↑Q : Set (PlE D.host)) → BlochKatoReduction.Gen.TrivAbove ψ₀ (D.ntw.l i) → (∃ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀) ∧ ∀ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀ → IntegralHeckeForms.TwOK i k Q (ψ.comp (D.ntw.art i Q)) := by
  intro D i k b v ρ Q ψ₀ hs hd ho ha hp hr ht
  refine ⟨?_, fun ψ hψ => twOK_of_reads (ρ := ρ) (fun g => hψ g) hs hd ho ha hp hr ht⟩
  obtain ⟨χ, hv, hχ⟩ := exists_reads (ρ := ρ) ψ₀ hp
  have hfin : IsOfFinOrder (D.ntw.zk i k) := isOfFinOrder_iff_pow_eq_one.2
    ⟨_, pow_pos (D.ntw.lPrime i).out.pos k, (IsPrimitiveRoot.coe_units_iff.mp (D.ntw.zk_prim i k)).pow_eq_one⟩
  haveI : Finite (Subgroup.zpowers (D.ntw.zk i k)) := finite_zpowers.2 hfin
  have hker : (χ.ker : Set (G D.host.E D.nd.Om)) = ψ₀.ker := Set.ext fun g => by
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    exact one_iff_of_reads hχ g
  obtain ⟨f, hf⟩ := D.ntw.art_univ i Q
    (fun u hu hl => Finset.disjoint_left.1 hd hu (D.ntw.twistExcludedPlaces_contains_residueChar i hl)) (Subgroup.zpowers (D.ntw.zk i k))
    (by
      rintro ⟨x, n, rfl⟩
      refine ⟨k, Subtype.ext ?_⟩
      change (D.ntw.zk i k ^ n) ^ (D.ntw.l i ^ k) = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        (IsPrimitiveRoot.coe_units_iff.mp (D.ntw.zk_prim i k)).pow_eq_one, one_zpow])
    (χ.codRestrict _ hv) (by rw [MonoidHom.ker_codRestrict, hker]; exact ho)
    (fun g g' h => Subtype.ext (by
      change χ g' = (χ g)⁻¹
      rw [← map_inv, eq_iff_of_reads hχ, map_inv]
      exact ha g g' h))
    (fun u hu A hA σ hσ => Subtype.ext (by
      change χ σ = 1
      rw [one_iff_of_reads hχ]
      by_contra hne
      exact hu ((hr u A hA).1 ⟨σ, hσ, hne⟩)))
  refine ⟨(Subgroup.zpowers (D.ntw.zk i k)).subtype.comp f, fun g => ?_⟩
  have h1 : f (D.ntw.art i Q g) = χ.codRestrict _ hv g := by rw [← hf]; rfl
  change ρ.emb _ = rd ρ (((f (D.ntw.art i Q g) : Subgroup.zpowers (D.ntw.zk i k)) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k)
  rw [h1]
  exact hχ g

end GlobalTheory.TwistDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassGroupDescentOfCoeffFieldTwistStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringClassGroup_descent_of_coeffFieldTwist : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v) (Q : Finset (PlE D.host)) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∀ u ∈ Q, IsSplitPl D.host u) → Disjoint Q (D.ntw.S0 i) → IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) → AntiHom D.ntw.cc ψ₀ → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → RamExactly ψ₀ (↑Q : Set (PlE D.host)) → BlochKatoReduction.Gen.TrivAbove ψ₀ (D.ntw.l i) → (∃ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀) ∧ ∀ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀ → IntegralHeckeForms.TwOK i k Q (ψ.comp (D.ntw.art i Q)) := by
  first | exact @GlobalTheory.TwistDescent.exists_pulls_twOK | exact GlobalTheory.TwistDescent.exists_pulls_twOK | (intros; apply GlobalTheory.TwistDescent.exists_pulls_twOK <;> assumption)
end
end
