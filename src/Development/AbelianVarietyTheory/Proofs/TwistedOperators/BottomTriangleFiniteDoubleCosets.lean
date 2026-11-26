module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleFiniteDoubleCosets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder Classical

namespace GlobalTheory.BotClassFin

variable {D : D7}

def finPart (V : HSp D) (g : GA D V) : GA D V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2.1

theorem continuous_finPart (V : HSp D) : Continuous (finPart V) :=
  continuous_subtype_val.comp (continuous_snd.comp (GlobalTheory.AdelicSplit.splitEquiv V).symm.continuous)

theorem finPart_mem (V : HSp D) (g : GA D V) : finPart V g ∈ GfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2.2

theorem finPart_one (V : HSp D) : finPart V 1 = 1 := by
  simp [finPart, map_one]

theorem finHom_finPart (V : HSp D) (g : GA D V) : finHom V (finPart V g) = finHom V g := by
  set p := (GlobalTheory.AdelicSplit.splitEquiv V).symm g with hp
  have e : g = p.1.1 * p.2.1 := ((GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g).symm
  have h1 : finHom V p.1.1 = 1 := p.1.2
  conv_rhs => rw [e]
  rw [map_mul, h1, one_mul]
  rfl

theorem exists_reps_of_open (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (GA D V))
    (hJ : IsOpen (J : Set (GA D V))) :
    ∃ H : Finset (GA D V), (∀ h ∈ H, h ∈ GfC V) ∧
      ∀ h ∈ GfC V, ∃ γ ∈ GQ V, ∃ r ∈ GinfC V, ∃ h₀ ∈ H, ∃ κ ∈ J, κ ∈ GfC V ∧ h = γ * r * h₀ * κ := by
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  set L : Subgroup (Bridge.Gf V) := (J ⊓ GfC V).map (finHom V).rangeRestrict with hL
  have hO : GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev V L := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev
    refine Subgroup.isOpen_of_mem_nhds (g := (1 : GA D V)) _ ?_
    have h1 : (finPart V) ⁻¹' (J : Set (GA D V)) ∈ nhds (1 : GA D V) := by
      refine (hJ.preimage (continuous_finPart V)).mem_nhds ?_
      show finPart V 1 ∈ J
      rw [finPart_one]
      exact J.one_mem
    refine Filter.mem_of_superset h1 fun g hg => ?_
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨finPart V g, ⟨hg, finPart_mem V g⟩, ?_⟩)
    exact Subtype.ext (finHom_finPart V g)
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover V hV L hO
  choose x hx using fun a => GlobalTheory.FunObj.ClassFin.gfcToGf_surjective V (c a)
  refine ⟨Finset.univ.image fun a => (x a).1, ?_, ?_⟩
  · intro h hh
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hh
    exact (x a).2
  · intro h hh
    obtain ⟨a, γ, k, e⟩ := hc ((finHom V).rangeRestrict h)
    obtain ⟨κ, ⟨hκJ, hκf⟩, hκ⟩ := Subgroup.mem_map.1 k.2
    have ex : finHom V (x a).1 = (c a).1 := congrArg Subtype.val (hx a)
    have ek : finHom V κ = k.1.1 := congrArg Subtype.val hκ
    have eγ : ((Bridge.ratF V γ : Bridge.Gf V) : _) = finHom V γ.1 := rfl
    have e' : finHom V h = finHom V γ.1 * finHom V (x a).1 * finHom V κ := by
      have := congrArg Subtype.val e
      rw [ex, ek, ← eγ]
      exact this
    refine ⟨γ.1, γ.2, γ.1⁻¹ * h * κ⁻¹ * (x a).1⁻¹, ?_, (x a).1, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩, κ, hκJ, hκf,
      by group⟩
    show finHom V _ = 1
    simp only [map_mul, map_inv, e']
    group

end GlobalTheory.BotClassFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsBesselFrameOfBesselDatumRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GramAtConjTranspose
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.ChainFr GlobalTheory.SepRows Matrix
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.SepPer

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem gramAt_conjTranspose (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  have h : (HSpace.gram V)ᴴ = HSpace.gram V := by
    funext i j
    exact V.herm.eq (V.frame j) (V.frame i)
  rw [gramAt, ← Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ), h]

end GlobalTheory.SepPer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsBesselFrameOfBesselDatumRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.BesselFrameReal

variable {D : D7}

theorem map_cT_gram_mul (V : HSp D) (τ : D.what₂.Tau) {a b : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E)
    (Z : Matrix (Fin V.rank) (Fin b) D.host.E) :
    (X.map (tauE D τ))ᴴ * gramAt D V τ * Z.map (tauE D τ) = (Xᴴ * V.gram * Z).map (tauE D τ) := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl

theorem map_cT_gram (V : HSp D) (τ : D.what₂.Tau) {a : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E) :
    (X.map (tauE D τ))ᴴ * gramAt D V τ = (Xᴴ * V.gram).map (tauE D τ) := by
  rw [Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl

theorem map_cT_gram_mulVec (V : HSp D) (τ : D.what₂.Tau) {a : ℕ} (X : Matrix (Fin V.rank) (Fin a) D.host.E)
    (z : Fin V.rank → D.host.E) :
    ((X.map (tauE D τ))ᴴ * gramAt D V τ) *ᵥ (fun k => tauE D τ (z k)) =
      fun i => tauE D τ (((Xᴴ * V.gram) *ᵥ z) i) := by
  funext i
  rw [map_cT_gram, RingHom.map_mulVec]
  rfl

theorem herm_gramAt (V : HSp D) (τ : D.what₂.Tau) (z : Fin V.rank → D.host.E) :
    Formalism.QuantumDeterminants.herm (gramAt D V τ) (fun k => tauE D τ (z k)) (fun k => tauE D τ (z k)) =
      tauE D τ (Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram z z) := by
  have hσ : ∀ x : D.host.E, tauE D τ ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = star (tauE D τ x) :=
    fun x => GlobalTheory.FockCompare.tauE_star τ x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.QuantumDeterminants.herm, Formalism.UG.hform, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, gramAt,
    Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

end GlobalTheory.BesselFrameReal

namespace GlobalTheory.BesselFrameReal

theorem linearIndependent_of_mul_eq_one {n r : ℕ} (e : Matrix (Fin n) (Fin r) ℂ) (L : Matrix (Fin r) (Fin n) ℂ)
    (hL : L * e = 1) : LinearIndependent ℂ eᵀ := by
  refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
  have h1 : e *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm] using this
  have h2 := congrArg (fun v => L *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
  exact congrFun h2

theorem isFrame_of_besDat : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ (d : BesDat A B ι) (τ : D.what₂.Tau),
  GlobalTheory.RealBessel.IsFrame (gramAt D B τ) (gramAt D A τ) ((frameMat B A ι).map (tauE D τ)) (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) := by
  intro D A B ι hι d τ
  have hinj : Function.Injective (tauE D τ) := (tauE D τ).injective
  have hunit : ∀ V : HSp D, IsUnit (gramAt D V τ) := fun V => by
    rw [Matrix.isUnit_iff_isUnit_det]
    show IsUnit ((tauE D τ).mapMatrix (HSpace.gram V)).det
    rw [← RingHom.map_det]
    exact isUnit_iff_ne_zero.2 ((map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V))
  obtain ⟨L, hL⟩ := GlobalTheory.BesselChar.exists_leftInv d.e d.e_iso.1
  refine
    { herm := GlobalTheory.SepPer.gramAt_conjTranspose B τ
      unit := hunit B
      unit₀ := hunit A
      codim := d.codim
      gram := ?_
      e_indep := ?_
      e_iso := ?_
      e_perp := ?_
      z_perpF := ?_
      z_perpE := ?_
      z_ne := ?_ }
  · rw [map_cT_gram_mul]
    have h : (frameMat B A ι)ᴴ * B.gram * frameMat B A ι = A.gram := GlobalTheory.AutFunCounterexample.gram_pull B A ι hι
    rw [h]; rfl
  · refine linearIndependent_of_mul_eq_one _ (L.map (tauE D τ)) ?_
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [map_cT_gram_mul]
    have h : d.eᴴ * B.gram * d.e = 0 := d.e_iso.2
    rw [h, Matrix.map_zero _ (map_zero _)]
  · rw [map_cT_gram_mul]
    have h : (frameMat B A ι)ᴴ * B.gram * d.e = 0 := d.e_perp
    rw [h, Matrix.map_zero _ (map_zero _)]
  · rw [map_cT_gram_mulVec]
    have h : ((frameMat B A ι)ᴴ * B.gram) *ᵥ d.z = 0 := d.z_perpA
    rw [h]; funext i; simp
  · rw [map_cT_gram_mulVec]
    have h : (d.eᴴ * B.gram) *ᵥ d.z = 0 := d.z_perpE
    rw [h]; funext i; simp
  · rw [herm_gramAt]
    exact (map_ne_zero _).2 d.z_ne

end GlobalTheory.BesselFrameReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsBesselFrameOfBesselDatumRealPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBesselFrame_of_besselDatum_realPlace : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ (d : BesDat A B ι) (τ : D.what₂.Tau),
  GlobalTheory.RealBessel.IsFrame (gramAt D B τ) (gramAt D A τ) ((frameMat B A ι).map (tauE D τ)) (d.e.map (tauE D τ)) (fun k => tauE D τ (d.z k)) := by
  first | exact @GlobalTheory.BesselFrameReal.isFrame_of_besDat | exact GlobalTheory.BesselFrameReal.isFrame_of_besDat | (intros; apply GlobalTheory.BesselFrameReal.isFrame_of_besDat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumPairCoordinateAlgebraic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.NormSum.CoordAlg

open Classical Formalism.UG Formalism.UG.P Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.IntOver GlobalTheory.NormSum.RepAt GlobalTheory.NormSum.PtsMem

theorem exists_prime_integralOver_gt (D : D7) (N : ℕ) (h : GA D N) (Q : ℕ) :
    ∃ p : ℕ, Q < p ∧ p.Prime ∧ IntegralOver D p h := by
  set g : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D) := ((h : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) with hg
  choose m hm0 hm using fun ij : Fin N × Fin N => denom (F := ℚ) (E := D.host.E) (g ij.1 ij.2)
  set M := ∏ ij, m ij with hMdef
  have hM0 : 0 < M := Finset.prod_pos fun ij _ => hm0 ij
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + Q + 1)
  have hpM' : ¬ p ∣ M := fun hd => by have := Nat.le_of_dvd hM0 hd; omega
  obtain ⟨v, hv, hw⟩ := exists_place p hp
  have hMv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro hm'
    obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM'))).map
      (Int.castRingHom (𝓞 ℚ))
    refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← e]
    exact add_mem (Ideal.mul_mem_left _ _ (by simpa using hm')) (Ideal.mul_mem_left _ _ (by simpa using hv))
  have hi : ∀ i j, afsplitEps D.host.E v * g i j ∈ OhE D := fun i j => eps_mul_mem v M hMv _ (by
    rw [hMdef, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_assoc]
    exact mul_mem (natCast_mem _ _) (hm (i, j)))
  obtain ⟨k, hk, hint, htriv⟩ := exists_int (F := ℚ) (D.host.conj : D.host.E →ₐ[ℚ] D.host.E) v
    (h : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) h.2 (Units.inv_eq_of_mul_eq_one_left ((mem_GA D _).1 h.2)) hi
  refine ⟨p, by omega, hp, ⟨k, hk⟩, (mem_intG _).2 hint, fun i j l => ?_⟩
  have := zero_at (F := ℚ) (E := D.host.E) v p hp hw (g i j - (1 : Matrix (Fin N) (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j) l
  rw [← htriv i j] at this
  exact this

end GlobalTheory.NormSum.CoordAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

namespace GlobalTheory.GramOneCompact

theorem isCompact_GinfC_of_gram_eq_one : ∀ (D : D7) (V : HSp D), V.gram = 1 → IsCompact (GinfC V : Set (GA D V)) := by
  intro D V hg
  have hL : (GlobalTheory.SW.stdL D.host.E V.rank).FG ∧ Submodule.span D.host.E
      (GlobalTheory.SW.stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨a, rfl⟩
    apply Submodule.subset_span
    exact ⟨a, by simp⟩
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.Ker.CongTop.exists_compact V _ hL.1 hL.2
  refine hC.of_isClosed_subset (GlobalTheory.Ker.CongTop.isClosed_GinfC V) fun k hk => hCm k ?_ (Or.inr hg)
  have hk1 : finHom V k = 1 := hk
  have h1 : GlobalTheory.Ker.fmt V k = GlobalTheory.Ker.fmt V 1 := by
    rw [GlobalTheory.Ker.CongTop.fmt_eq, GlobalTheory.Ker.CongTop.fmt_eq, hk1, map_one]
  rw [h1]
  exact (GlobalTheory.Ker.CongTop.congSub V (GlobalTheory.SW.stdL D.host.E V.rank) 1).one_mem.1

end GlobalTheory.GramOneCompact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitaryRealPoints_of_gram_eq_one : ∀ (D : D7) (V : HSp D), V.gram = 1 → IsCompact (GinfC V : Set (GA D V)) := by
  first | exact @GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one | exact GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one | (intros; apply GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomWeilActionFockPureTensorSubstituti
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomWeilActionFockPureTensorSubstituti
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BottomAct

open GlobalTheory.Grid (neg sgn ofSgn)

theorem conj_invT_of_unitary {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    ((M⁻¹).transpose).map (starRingEnd ℂ) = M := by
  rw [Matrix.inv_eq_left_inv h]
  ext a b
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]

theorem conj_invT_compAt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : V.gram = 1) (g : GA D V)
    (τ : D.what₂.Tau) :
    (((compAt θ τ (Formalism.L2.Theta.mt V g))⁻¹).transpose).map (starRingEnd ℂ) = compAt θ τ (Formalism.L2.Theta.mt V g) := by
  have h1 := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [hg, Matrix.mul_one] at h1
  exact conj_invT_of_unitary h1

theorem om_pureTensorO_bottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ (t : T) (g : GA D A) (P : MvPolynomial (FVar D WW.rank A.rank) ℂ), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) = pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B ((X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (X.f t)) (GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g)) P) := by
  intro D T L sc G W i j A A' WW X hX t g P
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => (hX.std.2.2 τ).2
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := (GlobalTheory.ConstRatio.theta_f hI t).1
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g) = Formalism.L2.Theta.mt A g := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g) with hu
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_one W.θ τ WW
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hom hθ
    (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rA.B (fun τ => X.rA.B τ * u τ) X.rW.s X.rW.s X.rW.B
    (fun τ => X.rW.B τ * 1) ((ofSgn true A).symm g) 1
    (fun τ => by rw [hmt, hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [one, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hmt, hBA, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [one, Matrix.one_mul, Matrix.mul_one]) (X.f t) hf P
  rw [hop.2]
  have hf' : IsThetaFunO W.ψ (neg A) WW ((X.ω t).toSgn true ((ofSgn true A).symm g, 1) (X.f t)) :=
    hom.om_pres _ _ hf
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have e2 : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  have key := GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ X.rA.B u X.rW.B (fun _ => 1) _ hf' P
  have hunit : ∀ τ, (((u τ)⁻¹).transpose).map (starRingEnd ℂ) = u τ := fun τ => conj_invT_compAt hθ hX.std.1 g τ
  have hv : (fun _ : D.what₂.Tau => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) = fun _ => 1 :=
    funext fun _ => Matrix.map_one _ (map_zero _) (map_one _)
  rw [funext hunit, hv] at key
  rw [e1, e2]
  exact key

end GlobalTheory.BottomAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomWeilActionFockPureTensorSubstitutiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_weilAction_fockPureTensor_substitution : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ (t : T) (g : GA D A) (P : MvPolynomial (FVar D WW.rank A.rank) ℂ), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) = pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B ((X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (X.f t)) (GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g)) P) := by
  first | exact @GlobalTheory.BottomAct.om_pureTensorO_bottom | exact GlobalTheory.BottomAct.om_pureTensorO_bottom | (intros; apply GlobalTheory.BottomAct.om_pureTensorO_bottom <;> assumption)
end
end
