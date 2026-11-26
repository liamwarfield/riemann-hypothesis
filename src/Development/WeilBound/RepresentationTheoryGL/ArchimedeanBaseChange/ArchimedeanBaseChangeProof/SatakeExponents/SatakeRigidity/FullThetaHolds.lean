module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRSplit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LWeightEx
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.AllPlaceRigidityResidual
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.IsTypeMap
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.GelfandKazhdanDualOfHyp
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LPermSub

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.TameCongruences.LocallyConstantOneCochain
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.DzCong.CongruenceClosure

theorem isSplitAt_of_deg_one {E : Type} [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (𝓞 E))
    (hf : v.asIdeal.inertiaDeg ℤ = 1) (he : v.asIdeal.ramificationIdx ℤ = 1) : IsSplitAt v := by
  classical
  have := v.isPrime
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have he' : v.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.ramificationIdx_tower (R := ℤ) (v.asIdeal.under (𝓞 (maximalRealSubfield E))) v.asIdeal
    rw [he] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hc := Formalism.IrreducibleCountingLemmas.Z.degree_one_split (maximalRealSubfield E) E h2 v.asIdeal v.ne_bot hf he'
  obtain ⟨P, Q, hne, hs⟩ := Set.ncard_eq_two.mp hc
  have hX : ∃ X ∈ (v.asIdeal.under (𝓞 (maximalRealSubfield E))).primesOver (𝓞 E), X ≠ v.asIdeal := by
    by_cases h : P = v.asIdeal
    · exact ⟨Q, hs ▸ Set.mem_insert_of_mem _ rfl, fun hQ => hne (h.trans hQ.symm)⟩
    · exact ⟨P, hs ▸ Set.mem_insert _ _, h⟩
  obtain ⟨X, hX, hXv⟩ := hX
  have hXb : X ≠ ⊥ := by
    rintro rfl
    have h0 : v.asIdeal.under (𝓞 (maximalRealSubfield E)) = ⊥ := hX.2.over.trans
      (Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ (𝓞 E)))
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h0)
  have := hX.1
  refine ⟨⟨X, hX.1, hXb⟩, fun h => hXv (congrArg HeightOneSpectrum.asIdeal h), ?_⟩
  ext1
  exact hX.2.over.symm

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

end PositivityTheory.Rg.DzCong.CongruenceClosure

namespace PositivityTheory.Rg.DzCong

end PositivityTheory.Rg.DzCong

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.OfEqOfIsSpeh
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem of_eq_of_isSpeh {w : HeightOneSpectrum (𝓞 E)} {N N' : ℕ} (σ : SmIrr (GL (Fin N) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin N') (w.adicCompletion E))) (x : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)) (d : ℕ)
    (h : GlobalTheory.LocGL.IsSpeh x d σ.ρ) (h' : GlobalTheory.LocGL.IsSpeh x d σ'.ρ) :
    GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred = GlobalTheory.LocGL.IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  obtain ⟨hd, hc⟩ := h
  obtain ⟨hd', hc'⟩ := h'
  obtain rfl : N = N' := hd.symm.trans hd'
  exact GlobalTheory.LocGL.IrrGL.of_eq_of.2 (GlobalTheory.LocGL.IsCosocle.unique hc' hc)

theorem ascEmb_of_sigma {N a a' d : ℕ} {V : Submodule ℂ (Sm E N)} (P : CuspSub E a) (P' : CuspSub E a')
    (h : ∀ P'' : CuspSub E a', P'.Iso P'' → AscEmb V P'' d)
    (e : (⟨a', CG.mk P'⟩ : Σ b, CG E b) = ⟨a, CG.mk P⟩) : AscEmb V P d := by
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp e
  exact h P (Quotient.exact (eq_of_heq he))

theorem rLoc : RLoc := by
  intro hJS hSS hStr E _ _ _ n D D' hr hr' hsat
  choose a d P ha hd hPu hPn hPs using hStr E n D hr
  choose a' d' P' ha' hd' hPu' hPn' hPs' using hStr E n D' hr'
  have he : ∀ i, AscEmb (D.V i) (P i) (d i) := fun i => hPs i (P i) (Setoid.refl (α := CuspSub E (a i)) (P i))
  have he' : ∀ j, AscEmb (D'.V j) (P' j) (d' j) := fun j =>
    hPs' j (P' j) (Setoid.refl (α := CuspSub E (a' j)) (P' j))
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E
  have h1 := Filter.eventually_all.2 fun i => hSS E (D.N i) (a i) (d i) (D.V i) (P i) (D.σ i) (D.pos i)
    (D.discrete i) (hPu i) (hPn i) (he i) (D.loc i) (fun k => GlobalTheory.HeckeGal.Model.absPow E (spehExp (d i) k))
    (fun k => hν _)
  have h2 := Filter.eventually_all.2 fun j => hSS E (D'.N j) (a' j) (d' j) (D'.V j) (P' j) (D'.σ j) (D'.pos j)
    (D'.discrete j) (hPu' j) (hPn' j) (he' j) (D'.loc j) (fun k => GlobalTheory.HeckeGal.Model.absPow E (spehExp (d' j) k))
    (fun k => hν _)
  obtain ⟨s, hs⟩ := GlobalTheory.Published.JacquetShalikaRigidity.unitary hJS (ι := Σ i, Fin (d i)) (κ := Σ j, Fin (d' j))
    (fun x => CG.mk (P x.1)) (fun y => CG.mk (P' y.1)) (fun x => ha x.1) (fun y => ha' y.1)
    (fun x => (CG.isUnitary_mk _).2 (hPu x.1)) (fun y => (CG.isUnitary_mk _).2 (hPu' y.1)) _ hν
    (fun x => spehExp (d x.1) x.2) (fun y => spehExp (d' y.1) y.2) (by
      filter_upwards [h1, h2, hsat] with w hw hw' hB
      obtain ⟨B, ⟨b, hb, hbB⟩, ⟨b', hb', hbB'⟩⟩ := hB
      choose c hc hsph hcs using hw
      choose c' hc' hsph' hcs' using hw'
      refine ⟨fun x => c x.1 x.2, fun y => c' y.1 y.2, fun x => hc x.1 x.2, fun y => hc' y.1 y.2, ?_⟩
      rw [Fintype.sum_sigma, Fintype.sum_sigma]
      have e1 : ∀ i, ∑ k, c i k = b i := fun i => (hcs i).unique (hb i).2
      have e2 : ∀ j, ∑ k, c' j k = b' j := fun j => (hcs' j).unique (hb' j).2
      simp only [e1, e2]
      exact hbB.trans hbB'.symm)
  have hstr := GlobalTheory.Rigid.strings_eq_of_equiv (fun i => (⟨a i, CG.mk (P i)⟩ : Σ b, CG E b)) d
    (fun j => (⟨a' j, CG.mk (P' j)⟩ : Σ b, CG E b)) d' s fun x => ⟨(hs x).1, (hs x).2⟩
  obtain ⟨s0, hs0⟩ := GlobalTheory.T.multiset_of_strings_determines_points_degrees _ d _ d' hd hd' hstr
  refine ⟨s0, fun i w => ?_⟩
  have hA : AscEmb (D'.V (s0 i)) (P i) (d i) := by
    rw [(hs0 i).2]
    exact ascEmb_of_sigma (P i) (P' (s0 i)) (hPs' (s0 i)) (hs0 i).1.symm
  obtain ⟨σ0, hσ0, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E (a i) (P i) w
  have k1 := ascSeed_holds2.2 E (D.N i) (a i) (d i) (D.V i) (P i) (D.pos i) (D.discrete i) (hPu i) (hPn i) (he i)
    w σ0 (D.σ i w) hσ0 (D.loc i w)
  have k2 := ascSeed_holds2.2 E (D'.N (s0 i)) (a i) (d i) (D'.V (s0 i)) (P i) (D'.pos _) (D'.discrete _) (hPu i)
    (hPn i) hA w σ0 (D'.σ (s0 i) w) hσ0 (D'.loc _ w)
  exact of_eq_of_isSpeh _ _ _ _ k1 k2

end PositivityTheory.Rg.BcB.F.Rig

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LStrSat
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

theorem spehExp_injective (d : ℕ) : Function.Injective (spehExp d) := fun i j h => by
  have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
    unfold spehExp at h
    linarith
  exact Fin.ext (by exact_mod_cast h')

theorem strSat : StrSat := by
  intro E _ _ _ N a d V P σ hN hV hPu hPn hA hloc ν hν
  have hd : 1 ≤ d := by
    obtain ⟨hsum, -⟩ := hA
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hsum
      omega
    · exact h
  have hex : ∀ s : ℝ, ∃ χ : Formalism.L2.Host.HChar E, χ.IsAbsPow s :=
    fun s => ⟨_, GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s⟩
  choose χ0 hχ0 using hex
  classical
  let μ : ℝ → Formalism.L2.Host.HChar E := fun s =>
    if h : ∃ k, spehExp d k = s then ν h.choose else χ0 s
  have hμ : ∀ s, (μ s).IsAbsPow s := fun s => by
    by_cases h : ∃ k, spehExp d k = s
    · simp only [μ, dif_pos h]
      have := hν h.choose
      rwa [h.choose_spec] at this
    · simp only [μ, dif_neg h]
      exact hχ0 s
  have hμk : ∀ k, μ (spehExp d k) = ν k := fun k => by
    have h : ∃ k', spehExp d k' = spehExp d k := ⟨k, rfl⟩
    simp only [μ, dif_pos h]
    rw [spehExp_injective d h.choose_spec]
  filter_upwards [GlobalTheory.SpehPair.eventually_spherical hV] with w hw
  have hsph := hw (σ w) (hloc w)
  obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (σ w).smooth (σ w).irred hsph
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E a P w
  have hS := PositivityTheory.Rg.Rs.ascSeed_holds2.2 E N a d V P hN hV hPu hPn hA w τ (σ w) hτ (hloc w)
  obtain ⟨B, hB, hBT⟩ := GlobalTheory.SpehPair.exists_sat_twist hd hτ hS hT μ hμ
  have hsum : ∑ k : Fin d, B k.rev = T := by
    rw [← hBT]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl
  refine ⟨fun k => B k.rev, fun k => ?_, hsph, hsum ▸ hT⟩
  have := hB k.rev
  rwa [PositivityTheory.Rg.Rs.satakeAscent.spehExp_rev, neg_neg, hμk, CG.twist_mk] at this

end PositivityTheory.Rg.BcB.F.Rig

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.TwistAbsPowAbsPow
noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

namespace GalX

open GlobalTheory.HeckeGal.Model (absPow absPow_isAbsPow)

theorem absPow_mul_absPow (E : Type) [Field E] [NumberField E] (x y : ℝ) :
    absPow E x * absPow E y = absPow E (x + y) := by
  refine Subtype.ext (MonoidHom.ext fun z => Units.ext ?_)
  change (((absPow E x).1 z : ℂˣ) : ℂ) * (((absPow E y).1 z : ℂˣ) : ℂ) = (((absPow E (x + y)).1 z : ℂˣ) : ℂ)
  rw [CG.absPow_val_apply, CG.absPow_val_apply, CG.absPow_val_apply, ← Complex.exp_add]
  push_cast
  ring_nf

theorem twist_absPow_absPow {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (P : CuspSub E a)
    (x y : ℝ) : (CG.mk (P.twist (absPow E x))).twist (absPow E y) = CG.mk (P.twist (absPow E (x + y))) := by
  rw [← absPow_mul_absPow]
  exact (CG.twist_mul (CG.mk P) _ _).symm

theorem infOfWeight_nodup {n : ℕ} (lam : DomWeight n) : (infOfWeight lam).Nodup := by
  unfold infOfWeight
  refine Multiset.Nodup.map (fun j k h => ?_) Finset.univ.nodup
  have h1 : (((lam.w j - (j : ℕ) : ℤ)) : ℂ) = ((lam.w k - (k : ℕ) : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  have h2 : lam.w j - (j : ℕ) = lam.w k - (k : ℕ) := Int.cast_injective h1
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · have := lam.anti hjk.le
    have : (j : ℕ) < k := hjk
    omega
  · rfl
  · have := lam.anti hjk.le
    have : (k : ℕ) < j := hjk
    omega

theorem mem_infOfWeight {n : ℕ} {lam : DomWeight n} {z : ℂ} (hz : z ∈ infOfWeight lam) :
    ∃ k : ℤ, z = k + ((n : ℂ) - 1) / 2 := by
  unfold infOfWeight at hz
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
  exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩

theorem prod_map_sum {ι α β : Type*} [CommMonoid β] (s : Finset ι) (M : ι → Multiset α) (f : α → β) :
    ((∑ i ∈ s, M i).map f).prod = ∏ i ∈ s, ((M i).map f).prod := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih => rw [Finset.sum_cons, Finset.prod_cons, Multiset.map_add (f := _), Multiset.prod_add, ih]

theorem regTw {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (D : Pre E n) (hr : D.Reg)
    (i : Fin D.c) {a d : ℕ} (P : CuspSub E a) (he : AscEmb (D.V i) P d) (k : Fin d) :
    (CG.mk (P.twist (absPow E (spehExp d k + ((a : ℝ) - n) / 2)))).IsRegAlg := by
  refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
  obtain ⟨lam, hlam⟩ := hr τ
  obtain ⟨m0, hm0, hsum⟩ := infAsc_holds E (D.N i) a d (D.V i) P (D.discrete i) he τ _ (D.inf i τ)
  set s : ℝ := spehExp d k + ((a : ℝ) - n) / 2 with hs
  have hexpo : ∀ τ, expo (absPow E s) τ = s :=
    (GlobalTheory.CuspRep.InfType.expo_of_infType E _).2.1 s (absPow_isAbsPow E s)
  have hm' : (P.twist (absPow E s)).HasInfChar τ (m0.map (· + (s : ℂ))) := by
    have := hm0.twist (absPow E s)
    rwa [hexpo] at this
  rw [CG.HasInfChar.infChar_eq (π := CG.mk _) hm']
  have hle : D.m i τ ≤ infOfWeight lam := by
    rw [← hlam]
    exact Finset.single_le_sum (f := fun j => D.m j τ) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
  have hk : m0.map (· + (spehExp d k : ℂ)) ≤ D.m i τ := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun j : Fin d => m0.map (· + (spehExp d j : ℂ))) (fun _ _ => Multiset.zero_le _)
      (Finset.mem_univ k)
  have hnd : (m0.map (· + (spehExp d k : ℂ))).Nodup := Multiset.nodup_of_le (hk.trans hle) (infOfWeight_nodup lam)
  refine ⟨(Multiset.Nodup.of_map _ hnd).map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨j, hj⟩ := mem_infOfWeight (Multiset.mem_of_le (hk.trans hle) (Multiset.mem_map_of_mem _ hy))
  refine ⟨j, ?_⟩
  rw [hs]
  push_cast
  linear_combination hj

end GalX

end PositivityTheory.Rg.BcB.F.Rig

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRCuspCsd
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

namespace CuspidalConjugateSelfDual

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hasInfChar_thetaSub {a : ℕ} (P : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ)
    (hm : P.HasInfChar (ComplexEmbedding.conjugate τ) m) :
    (GlobalTheory.ThetaPull.thetaSub P).HasInfChar τ (m.map Neg.neg) := by
  refine ⟨by rw [Multiset.card_map, hm.1], ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (GlobalTheory.ThetaPull.pull E a φ) = _ • GlobalTheory.ThetaPull.pull E a φ
  rw [GlobalTheory.ThetaPull.cap_pull, LinearMap.smul_apply, hm.2 _ φ hφ, smul_smul, map_smul]
  congr 1
  have e : ((m.map Neg.neg).map (u + ·)) = (m.map (-u + ·)).map Neg.neg := by
    rw [Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    ring
  rw [e, Multiset.prod_map_neg, Multiset.card_map, hm.1]

theorem conj_of_mem_infOfWeight {n : ℕ} (lam : DomWeight n) {x : ℂ} (hx : x ∈ infOfWeight lam) :
    (starRingEnd ℂ) x = x := by
  obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
  simp [map_div₀, map_ofNat]

theorem hasInfChar_of_sigma {a b : ℕ} {π : CuspSub E a} {π' : CuspSub E b}
    (h : (⟨a, CG.mk π⟩ : Σ c, CG E c) = ⟨b, CG.mk π'⟩) {τ : E →+* ℂ} {m : Multiset ℂ} (hm : π.HasInfChar τ m) :
    π'.HasInfChar τ m := by
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp h
  have hi : π.Iso π' := Quotient.exact (eq_of_heq he)
  exact hi.hasInfChar hm

theorem isCsd_of_sigma {a b : ℕ} {π : CuspSub E a} {π' : CuspSub E b}
    (h : (⟨a, π⟩ : Σ c, CuspSub E c) = ⟨b, π'⟩) (hc : π.IsCsd) : π'.IsCsd := by
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp h
  obtain rfl := eq_of_heq he
  exact hc

theorem isCsd_of_sigma_theta {a : ℕ} {π : CuspSub E a}
    (h : (⟨a, CG.mk (GlobalTheory.ThetaPull.thetaSub π)⟩ : Σ c, CG E c) = ⟨a, CG.mk π⟩) : π.IsCsd :=
  GlobalTheory.ThetaPull.isCsd_of_iso (Quotient.exact (eq_of_heq (Sigma.mk.inj h).2))

theorem conjPl_cw (w : HeightOneSpectrum (𝓞 E)) : ConjPl w (GlobalTheory.ThetaSatake.cw w) := by
  refine ⟨GlobalTheory.DefU.LocRet.under_conjSrc w, ?_⟩
  by_cases h : GlobalTheory.ThetaSatake.cw w = w
  · exact Or.inr ((GlobalTheory.ConjAtPlace.conjSrc_eq_iff w).1 h)
  · exact Or.inl h

theorem map_inv_sum {ι : Type} [Fintype ι] (f : ι → Multiset ℂˣ) :
    (∑ i, f i).map (·⁻¹) = ∑ i, (f i).map (·⁻¹) :=
  map_sum (Multiset.mapAddMonoidHom (·⁻¹)) f Finset.univ

theorem sum_rev_map {d : ℕ} (f : Fin d → Multiset ℂˣ) :
    ∑ k : Fin d, (f k.rev).map (·⁻¹) = (∑ k, f k).map (·⁻¹) := by
  rw [map_inv_sum]
  exact Fintype.sum_equiv Fin.revPerm _ _ fun k => by rw [Fin.revPerm_apply]


variable (E) in
def nuT (s : ℝ) : Formalism.L2.Host.HChar E := GlobalTheory.ThetaPull.thetaChar (GlobalTheory.HeckeGal.Model.absPow E (-s))

theorem isAbsPow_nuT (s : ℝ) : (nuT E s).IsAbsPow s := by
  have h := GlobalTheory.ThetaPull.isAbsPow_thetaChar (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (-s))
  rwa [neg_neg] at h


variable (E) in
def muT (d : ℕ) (k : Fin d) : Formalism.L2.Host.HChar E := GlobalTheory.HeckeGal.Model.absPow E (-spehExp d k.rev)

omit [IsCMField E] in
theorem isAbsPow_muT (d : ℕ) (k : Fin d) : (muT E d k).IsAbsPow (spehExp d k) := by
  have e : -spehExp d k.rev = spehExp d k := by rw [InfinitesimalCharacterAscent.spehExp_rev, neg_neg]
  show (GlobalTheory.HeckeGal.Model.absPow E (-spehExp d k.rev)).IsAbsPow (spehExp d k)
  rw [e]
  exact GlobalTheory.HeckeGal.Model.absPow_isAbsPow E _

end CuspidalConjugateSelfDual


open CuspidalConjugateSelfDual in
theorem rCuspCsd : RCuspCsd := by
  intro hJ hSS hStr E _ _ _ n D hr ht i a d P ha hd hu hn he
  have hx : ∀ j, ∃ (a' d' : ℕ) (P' : CuspSub E a'), 1 ≤ a' ∧ 1 ≤ d' ∧ P'.IsUnitary ∧ IsNormalised P' ∧
      AscEmb (D.V j) P' d' ∧ (j = i → (⟨a', P'⟩ : Σ b, CuspSub E b) = ⟨a, P⟩) := fun j => by
    by_cases h : j = i
    · subst h
      exact ⟨a, d, P, ha, hd, hu, hn, he, fun _ => rfl⟩
    · obtain ⟨a', d', P', h1, h2, h3, h4, h5⟩ := hStr E n D hr j
      exact ⟨a', d', P', h1, h2, h3, h4, h5 P' (Setoid.refl (α := CuspSub E a') P'), fun e => absurd e h⟩
  choose A Dd PP hA hDd hU hN hE hI using hx
  have hW : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ j, ∃ b : Fin (Dd j) → Multiset ℂˣ,
      (∀ k, (CG.mk ((PP j).twist (nuT E (spehExp (Dd j) k)))).HasSat w (b k)) ∧
      GlobalTheory.LGrp.IsSpherical (D.σ j w).ρ (GlobalTheory.LFun.KGL w (n := (D.N j))) ∧ GlobalTheory.LFun.HasSatGL w (D.σ j w).ρ (∑ k, b k) :=
    Filter.eventually_all.2 fun j => hSS E (D.N j) (A j) (Dd j) (D.V j) (PP j) (D.σ j) (D.pos j) (D.discrete j)
      (hU j) (hN j) (hE j) (D.loc j) (fun k => nuT E (spehExp (Dd j) k)) (fun k => isAbsPow_nuT _)
  have hinj : Function.Injective (GlobalTheory.ThetaSatake.cw (E := E)) :=
    Function.LeftInverse.injective (g := GlobalTheory.ThetaSatake.cw) fun v => GlobalTheory.ThetaPull.conjSrc_conjSrc v
  have hC : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ j, ∃ c : Fin (Dd j) → Multiset ℂˣ,
      (∀ k, (CG.mk ((PP j).twist (muT E (Dd j) k))).HasSat (GlobalTheory.ThetaSatake.cw w) (c k)) ∧
      GlobalTheory.LGrp.IsSpherical (D.σ j (GlobalTheory.ThetaSatake.cw w)).ρ (GlobalTheory.LFun.KGL (GlobalTheory.ThetaSatake.cw w) (n := (D.N j))) ∧
      GlobalTheory.LFun.HasSatGL (GlobalTheory.ThetaSatake.cw w) (D.σ j (GlobalTheory.ThetaSatake.cw w)).ρ (∑ k, c k) :=
    hinj.tendsto_cofinite.eventually (Filter.eventually_all.2 fun j => hSS E (D.N j) (A j) (Dd j) (D.V j) (PP j)
      (D.σ j) (D.pos j) (D.discrete j) (hU j) (hN j) (hE j) (D.loc j) (fun k => muT E (Dd j) k)
      (fun k => isAbsPow_muT _ _))
  obtain ⟨s, hs⟩ := hJ.unitary (ι := Σ j, Fin (Dd j)) (κ := Σ j, Fin (Dd j)) (m := fun x => A x.1)
    (m' := fun x => A x.1) (fun x => CG.mk (GlobalTheory.ThetaPull.thetaSub (PP x.1))) (fun x => CG.mk (PP x.1))
    (fun x => hA x.1) (fun x => hA x.1)
    (fun x => (CG.isUnitary_mk _).2 (GlobalTheory.SpehPair.isUnitary_of_isNormalised
      (GlobalTheory.ThetaPull.isNormalised_thetaSub (hN x.1))))
    (fun x => (CG.isUnitary_mk _).2 (hU x.1)) (nuT E) isAbsPow_nuT (fun x => spehExp (Dd x.1) x.2)
    (fun x => spehExp (Dd x.1) x.2) (by
      filter_upwards [hW, hC, ht] with w hw hc hθ
      choose b hb1 hb2 hb3 using hw
      choose c hc1 hc2 hc3 using hc
      obtain ⟨Bt, ⟨bw, hbw, hbsum⟩, hconj⟩ := hθ
      obtain ⟨bc, hbc, hbcsum⟩ := hconj _ (conjPl_cw w)
      have e1 : ∀ j, bw j = ∑ k, b j k := fun j => GlobalTheory.LFun.HasSatGL.unique (hbw j).2 (hb3 j)
      have e2 : ∀ j, bc j = ∑ k, c j k := fun j => GlobalTheory.LFun.HasSatGL.unique (hbc j).2 (hc3 j)
      refine ⟨fun x => (c x.1 x.2.rev).map (·⁻¹), fun x => b x.1 x.2, fun x => ?_, fun x => hb1 x.1 x.2, ?_⟩
      · have h := hc1 x.1 x.2.rev
        simp only [muT, Fin.rev_rev] at h
        show ((CG.mk (GlobalTheory.ThetaPull.thetaSub (PP x.1))).twist (GlobalTheory.ThetaPull.thetaChar
          (GlobalTheory.HeckeGal.Model.absPow E (-spehExp (Dd x.1) x.2)))).HasSat w ((c x.1 x.2.rev).map (·⁻¹))
        rw [CG.twist_mk, ← GlobalTheory.ThetaPull.thetaSub_twist]
        exact GlobalTheory.ThetaSatake.hasSat_thetaSub _ w _ h
      · rw [Fintype.sum_sigma, Fintype.sum_sigma, Finset.sum_congr rfl fun j _ => sum_rev_map (c j),
          ← map_inv_sum (fun j => ∑ k, c j k), ← Finset.sum_congr rfl fun j _ => e2 j,
          ← Finset.sum_congr rfl fun j _ => e1 j, hbcsum, hbsum, Multiset.map_map]
        simp)
  have hstr := GlobalTheory.Rigid.strings_eq_of_equiv
    (fun j => (⟨A j, CG.mk (GlobalTheory.ThetaPull.thetaSub (PP j))⟩ : Σ b, CG E b)) Dd
    (fun j => (⟨A j, CG.mk (PP j)⟩ : Σ b, CG E b)) Dd s fun x => hs x
  obtain ⟨s0, hs0⟩ := GlobalTheory.T.multiset_of_strings_determines_points_degrees _ Dd _ Dd hDd hDd hstr
  have hfix : s0 i = i := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨lam, hlam⟩ := hr τ
    obtain ⟨m0, hm0, e0⟩ := infAsc_holds E (D.N i) (A i) (Dd i) (D.V i) (PP i) (D.discrete i) (hE i) τ _
      (D.inf i τ)
    obtain ⟨m1, hm1, -⟩ := infAsc_holds E (D.N i) (A i) (Dd i) (D.V i) (PP i) (D.discrete i) (hE i)
      (ComplexEmbedding.conjugate τ) _ (D.inf i _)
    obtain ⟨m2, hm2, e2⟩ := infAsc_holds E (D.N (s0 i)) (A (s0 i)) (Dd (s0 i)) (D.V (s0 i)) (PP (s0 i))
      (D.discrete _) (hE _) τ _ (D.inf _ τ)
    obtain ⟨μ, hμ1, hμ2⟩ := GlobalTheory.T.exists_right_haar_measure E (A i)
    have := hμ1
    have := hμ2
    obtain ⟨B, hB⟩ := GlobalTheory.T.exists_invariant_hermitian_form PositivityTheory.Rg.HF.GL.cuspFormsBoundedGL E (A i) μ (PP i) (hN i)
    have hconj := GlobalTheory.T.infinitesimal_character_conjugate E (A i) (PP i) B hB τ m0 m1 hm0 hm1
    have hθ := hasInfChar_of_sigma (hs0 i).1 (hasInfChar_thetaSub (PP i) τ m1 hm1)
    have hmem : ∀ z ∈ m0, z + (spehExp (Dd i) ⟨0, hDd i⟩ : ℂ) ∈ D.m i τ := fun z hz => by
      rw [e0]
      exact Multiset.mem_sum.2 ⟨⟨0, hDd i⟩, Finset.mem_univ _, Multiset.mem_map_of_mem _ hz⟩
    have hreal : ∀ z ∈ m0, (starRingEnd ℂ) z = z := fun z hz => by
      have h1 : z + (spehExp (Dd i) ⟨0, hDd i⟩ : ℂ) ∈ ∑ j, D.m j τ :=
        Multiset.mem_of_le (Finset.single_le_sum (f := fun j => D.m j τ) (fun _ _ => Multiset.zero_le _)
          (Finset.mem_univ i)) (hmem z hz)
      rw [hlam] at h1
      have h2 := conj_of_mem_infOfWeight lam h1
      rw [map_add (f := _), Complex.conj_ofReal] at h2
      exact add_right_cancel h2
    have h20 : m2 = m0 := by
      rw [hm2.unique hθ, hconj, Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id m0]
      refine Multiset.map_congr rfl fun z hz => ?_
      simp [hreal z hz]
    have heq : D.m i τ = D.m (s0 i) τ := by
      rw [e0, e2, h20, (hs0 i).2]
    have hne : D.m i τ ≠ 0 := by
      obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.1 (by rw [hm0.1]; exact hA i)
      exact fun h0 => by simpa [h0] using hmem z hz
    exact (GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin D.c) (fun j => D.m j τ)
      (by rw [hlam]; exact GlobalTheory.DefiniteBC.nodup_infOfWeight lam) i (s0 i) hne heq).symm
  have hcsd : (PP i).IsCsd := isCsd_of_sigma_theta (by have h := (hs0 i).1; rwa [hfix] at h)
  exact isCsd_of_sigma (hI i rfl) hcsd

end PositivityTheory.Rg.BcB.F.Rig

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LSplitConj
noncomputable section

open NumberField IsDedekindDomain Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


omit [IsCMField E] in
theorem sc_hasSatGL_of_isSubquotient {w : HeightOneSpectrum (𝓞 E)} {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (hρs : IsSmooth ρ)
    (σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W) (hsub : GlobalTheory.SmGL.IsSubquotient σ ρ)
    (hsph : GlobalTheory.LGrp.IsSpherical σ (GlobalTheory.LFun.KGL w (n := n))) (B : Multiset ℂˣ)
    (hsat : ∀ f ∈ fixed ρ (GlobalTheory.LFun.KGL w (n := n)), f ≠ 0 → GlobalTheory.LFun.IsSatVecGL w ρ f B) :
    GlobalTheory.LFun.HasSatGL w σ B := by
  obtain ⟨S, q, hq⟩ := hsub
  obtain ⟨-, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  have hSs : IsSmooth S.toRepresentation := fun y => by
    refine (congrArg IsOpen ?_).mpr (hρs y.1)
    ext g
    exact Subtype.ext_iff
  refine ⟨hsph, fun x hx hx0 => ?_⟩
  have hx' : x ∈ (fixed S.toRepresentation (GlobalTheory.LFun.KGL w (n := n))).map q.toLinearMap := by
    rw [GlobalTheory.LocGL.map_fixed_of_surjective hSs hKc (f := q) hq]
    exact hx
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 hx'
  have hu0 : u ≠ 0 := fun e => hx0 (by rw [← hux, e, map_zero])
  have huK : u.1 ∈ fixed ρ (GlobalTheory.LFun.KGL w (n := n)) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hu k hk)
  have hu1 : GlobalTheory.LFun.IsSatVecGL w ρ u.1 B := hsat _ huK fun e => hu0 (Subtype.ext e)
  have hu2 : GlobalTheory.LFun.IsSatVecGL w S.toRepresentation u B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := ρ) S.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective hu1
  have hu3 : GlobalTheory.LFun.IsSatVecGL w σ (q.toLinearMap u) B :=
    hu2.map (ρ' := σ) q.toLinearMap (fun g y => Representation.IntertwiningMap.isIntertwining _ _ q g y)
      (by rw [hux]; exact hx0)
  rw [hux] at hu3
  exact hu3

theorem sc_satVec (X : Pre E n) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (h : X.Sat w B) :
    ∀ f ∈ fixed (locProd X.h w (X.σ · w)) (GlobalTheory.LFun.KGL w (n := n)), f ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w (locProd X.h w (X.σ · w)) f B := by
  obtain ⟨b, hb, rfl⟩ := h
  intro f hf hf0
  obtain ⟨S, hS, hfS⟩ := GlobalTheory.SatInd.exists_sat_multiProd X.h (π := fun i => (X.σ i w).ρ)
    (fun i => (X.σ i w).smooth) (fun i => (X.σ i w).irred) hf hf0
  have e : S = b := funext fun a => (hS a).unique (hb a).2
  rw [← e]
  exact hfS

theorem sc_cLoc_conj (x : UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    cLoc u x = GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n (cLoc (GlobalTheory.ThetaSatake.cw u) x) := by
  have h : ((GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)
      (cLoc (GlobalTheory.ThetaSatake.cw u) x)).val)ᵀ * (cLoc u x).val = 1 := GlobalTheory.SplitPts.comp_eq x u
  generalize hM : GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)
      (cLoc (GlobalTheory.ThetaSatake.cw u) x) = M at h
  have h1 : ((M⁻¹ : GL (Fin n) (u.adicCompletion E)).val)ᵀ * (M.val)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have h2 : (cLoc u x).val = ((M⁻¹ : GL (Fin n) (u.adicCompletion E)).val)ᵀ := by
    calc (cLoc u x).val = ((M⁻¹ : GL (Fin n) (u.adicCompletion E)).val)ᵀ * ((M.val)ᵀ * (cLoc u x).val) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = _ := by rw [h, Matrix.mul_one]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [h2, GlobalTheory.LFun.ConjPlace.invT_val, Matrix.transpose_apply, ← hM, ← map_inv]
  rfl

theorem splitConj : SplitConj := by
  intro E _ _ _ n π hπ D w u hw hwu hu hDw hDu B B' hB hB'
  obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hw
  have huw : u ≠ w := hwu.2.resolve_right (not_not.2 hw)
  have hu' : u = conjSrc (GlobalTheory.SplitPts.conjE E) w := (hover u hwu.1).resolve_left huw
  have hw' : w = GlobalTheory.ThetaSatake.cw u := by
    rw [hu']
    exact (GlobalTheory.SplitPts.conjSrc_conjSrc_cm w).symm
  clear hu' hover
  subst hw'
  obtain ⟨P, hPsub, hPc⟩ := hDw
  obtain ⟨P', hP'sub, hP'c⟩ := hDu
  have hPsat : GlobalTheory.LFun.HasSatGL (GlobalTheory.ThetaSatake.cw u) P.ρ B :=
    sc_hasSatGL_of_isSubquotient (locProd D.h _ (D.σ · _)) (GlobalTheory.SmGL.isSmooth_parInd _ _) P.ρ hPsub
      (GlobalTheory.PfBCI.split_spherical hπ hw P hPc hu) B (sc_satVec D _ B hB)
  have hq : Formalism.UG.qV E u = Formalism.UG.qV E (GlobalTheory.ThetaSatake.cw u) := (GlobalTheory.ThetaSatake.absNorm_cw u).symm
  have hQsat : GlobalTheory.LFun.HasSatGL u
      (P.ρ.comp (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm.toMonoidHom) (B.map (·⁻¹)) :=
    GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc u) (conjLoc_spec _ u).2.2 hq (LinearEquiv.refl ℂ P.V)
      (fun g x => by
        show P.ρ ((GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm
          (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n g)) x = P.ρ g x
        rw [MulEquiv.symm_apply_apply]) hPsat
  have hloc : locU n u = locU n (GlobalTheory.ThetaSatake.cw u) := by
    simp only [locU, hwu.1]
  have hQc : IsCompAlong π (locU n u) ((cLoc u).comp (locU n u).subtype)
      (P.ρ.comp (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm.toMonoidHom) := by
    obtain ⟨hirr, f, hf0, hfm, hf⟩ := hPc
    refine ⟨GlobalTheory.PfBCI.SplitSph.isIrreducible_comp_surj P.ρ _
      (GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm.surjective hirr, f, hf0, hfm, fun x v => ?_⟩
    have hx : (x : UA E n) ∈ locU n (GlobalTheory.ThetaSatake.cw u) := hloc ▸ x.2
    have e := hf ⟨x, hx⟩ v
    show f (P.ρ ((GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc u) n).symm (cLoc u (x : UA E n))) v) =
      RU E n (x : UA E n) (f v)
    rw [sc_cLoc_conj (x : UA E n) u, MulEquiv.symm_apply_apply]
    exact e
  have hsu : IsSplitAt u := ⟨GlobalTheory.ThetaSatake.cw u, Ne.symm huw, hwu.1.symm⟩
  have hP'inv : GlobalTheory.LFun.HasSatGL u P'.ρ (B.map (·⁻¹)) :=
    GlobalTheory.SplitSatake.hasSatGL_of_isCompAlong_split E n π hπ u hsu _ _ _ P'.ρ hQc hP'c _ hQsat
  have hP'B' : GlobalTheory.LFun.HasSatGL u P'.ρ B' :=
    sc_hasSatGL_of_isSubquotient (locProd D.h u (D.σ · u)) (GlobalTheory.SmGL.isSmooth_parInd _ _) P'.ρ hP'sub hP'inv.1 B'
      (sc_satVec D u B' hB')
  exact hP'B'.unique hP'inv

end PositivityTheory.Rg.BcB.F.Rig

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LInertSatExb
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.F.Rig.B

theorem inertSatEx : InertSatEx := by
  intro E _ _ _ hE n π hπ w hw hu
  exact GlobalTheory.BcSpehCompare.exists_hasSatAt (fun v => hE v) hπ hw hu

end PositivityTheory.Rg.BcB.F.Rig.B

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LRFull
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.One

namespace PositivityTheory.Rg.BcB.F.Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem rfull_finite_under_eq (u : HeightOneSpectrum (𝓞 E)) :
    {w : HeightOneSpectrum (𝓞 E) |
      w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))}.Finite := by
  have hm : (u.under (𝓞 (maximalRealSubfield E))).asIdeal.IsMaximal := (u.under _).isMaximal
  refine (Set.Finite.preimage (f := HeightOneSpectrum.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)
    (IsDedekindDomain.primesOver_finite (u.under (𝓞 (maximalRealSubfield E))).asIdeal (𝓞 E))).subset ?_
  intro w hw
  exact ⟨w.isPrime, ⟨by rw [← hw]; rfl⟩⟩

theorem rfull_eventually_sat (D : Pre E n) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, D.Sat w B := by
  have h : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∀ i, GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (n := (D.N i))) :=
    Filter.eventually_all.2 fun i =>
      (GlobalTheory.SpehPair.eventually_spherical (D.discrete i)).mono fun w hw => hw _ (D.loc i w)
  refine h.mono fun w hw => ?_
  choose b hb using fun i =>
    GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (D.σ i w).smooth (D.σ i w).irred (hw i)
  exact ⟨∑ i, b i, b, fun i => ⟨hw i, hb i⟩, rfl⟩

theorem rfull_bcParam_map_inv (n : ℕ) (α : Fin (n / 2) → ℂˣ) :
    (GlobalTheory.LGrp.bcParam n α).map (·⁻¹) = GlobalTheory.LGrp.bcParam n α := by
  simp only [GlobalTheory.LGrp.bcParam, Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, inv_inv,
    Multiset.map_replicate, inv_one]
  rw [add_comm (Multiset.map _ _) (Multiset.map _ _)]

theorem rFullSat : RFullSat := by
  intro hU hI hS E _ _ _ hE n π hπ D D' hD hD'
  filter_upwards [hU E n π hπ, hS E n π hπ D D' hD.1.2 hD'.1.2] with w hu hsp
  by_cases hw : IsSplitAt w
  · exact hsp hw
  · obtain ⟨s, ϖ, q, α, hs, hinv, hα⟩ := hI E hE n π hπ w hw hu
    obtain ⟨B, hB, hBα⟩ := hD.2 w hu hw
    obtain ⟨B', hB', hBα'⟩ := hD'.2 w hu hw
    refine ⟨B, hB, ?_⟩
    rw [hBα s ϖ q hs hinv α hα, ← hBα' s ϖ q hs hinv α hα]
    exact hB'

theorem rFullTheta : RFullTheta := by
  intro hU hI hC E _ _ _ hE n π hπ D hD
  have hbad : {u : HeightOneSpectrum (𝓞 E) |
      ¬ ((∃ B, D.Sat u B) ∧ (IsSplitAt u → D.SplitAt π u))}.Finite := by
    refine ((Filter.eventually_cofinite.1 (rfull_eventually_sat D)).union hD.1.2).subset ?_
    intro u hu
    by_cases h1 : ∃ B, D.Sat u B
    · right
      by_contra h2
      exact hu ⟨h1, fun hs => by_contra fun h3 => h2 ⟨hs, h3⟩⟩
    · left
      exact h1
  have hconj : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ u, ConjPl w u →
      (∃ B, D.Sat u B) ∧ (IsSplitAt u → D.SplitAt π u) := by
    rw [Filter.eventually_cofinite]
    refine (hbad.biUnion fun u _ => rfull_finite_under_eq u).subset ?_
    intro w hw
    have hw' : ¬ ∀ u, ConjPl w u → (∃ B, D.Sat u B) ∧ (IsSplitAt u → D.SplitAt π u) := hw
    obtain ⟨u, hu⟩ := not_forall.1 hw'
    obtain ⟨hc, hu'⟩ := Classical.not_imp.1 hu
    exact Set.mem_biUnion hu' hc.1.symm
  have hsp0 : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ¬ (IsSplitAt w ∧ ¬ D.SplitAt π w) :=
    Filter.eventually_cofinite.2 (hD.1.2.subset fun x hx => not_not.1 hx)
  filter_upwards [hU E n π hπ, rfull_eventually_sat D, hconj, hsp0]
    with w hu hs hc hsp
  by_cases hw : IsSplitAt w
  · obtain ⟨B, hB⟩ := hs
    refine ⟨B, hB, fun u hwu => ?_⟩
    obtain ⟨⟨B', hB'⟩, hsu⟩ := hc u hwu
    have hus : IsSplitAt u := ⟨w, (hwu.2.resolve_right (not_not_intro hw)).symm, hwu.1.symm⟩
    have hsw : D.SplitAt π w := by
      by_contra h
      exact hsp ⟨hw, h⟩
    have e := hC E n π hπ D w u hw hwu hu hsw (hsu hus) B B' hB hB'
    rw [← e]
    exact hB'
  · obtain ⟨s, ϖ, q, α, hs', hinv, hα⟩ := hI E hE n π hπ w hw hu
    obtain ⟨B, hB, hBα⟩ := hD.2 w hu hw
    refine ⟨B, hB, fun u hwu => ?_⟩
    have hu' : u = w := by
      by_contra hne
      exact hw ⟨u, hne, hwu.1⟩
    subst hu'
    have e := hBα s ϖ q hs' hinv α hα
    rw [e, rfull_bcParam_map_inv, ← e]
    exact hB

end PositivityTheory.Rg.BcB.F.Rig

end
end

namespace PositivityTheory.Rg.BcB.F.Rig

open PositivityTheory.Rg.BcB.One

theorem strings_holds : Strings := rStrings regPart

theorem cuspCsd_holds : CuspCsd := rCuspCsd PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity strSat strings_holds

theorem locRigid_holds : LocRigid := rLoc PositivityTheory.AdelicQuotientData.jacquetShalikaRigidity strSat strings_holds

theorem unrAE_holds : UnrAE := fun _ _ _ _ _ _ hπ => eventually_isUnramU hπ

theorem fullSat_holds : FullSat := rFullSat unrAE_holds B.inertSatEx splitSatPre

theorem fullTheta_holds : FullTheta := rFullTheta unrAE_holds B.inertSatEx splitConj

theorem fieldN_of_run (hR : RunFin) : PositivityTheory.Rg.BcN.BaseChangeIsobaricN :=
  fieldN_of hR fullSat_holds fullTheta_holds weightEx strings_holds cuspCsd_holds locRigid_holds permSub

end PositivityTheory.Rg.BcB.F.Rig
