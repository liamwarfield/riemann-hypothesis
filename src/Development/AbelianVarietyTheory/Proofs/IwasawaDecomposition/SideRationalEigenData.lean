module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptySpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientLinearLiftDoubleCosetOperators
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefImPartOnPolydiscOfPuncturedCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedStdLatticeEqDecoratedLatticeReindexed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRingActsFaithfullyOnLocalisedLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBaseChangeFreeOverLocalisationCoeffRing
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBaseChangeFreeOverLocalisationCoeffRing
noncomputable section
namespace GlobalTheory.FreeDedekindQuotient

variable {A O : Type} [CommRing A] [CommRing O] {ι : Type} [Fintype ι] [DecidableEq ι]

def bcEnd (s : A →+* O) (e : (ι → A) →ₗ[A] (ι → A)) : (ι → O) →ₗ[O] (ι → O) where
  toFun y := ∑ k, y k • (fun i => s (e (Pi.single k 1) i))
  map_add' y z := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c y := by simp [mul_smul, Finset.smul_sum]

theorem bcEnd_comp (s : A →+* O) (e : (ι → A) →ₗ[A] (ι → A)) (r : ι → A) :
    bcEnd s e (s ∘ r) = s ∘ e r := by
  have hr : r = ∑ k, r k • (Pi.single k 1 : ι → A) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hr]
  ext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [bcEnd, Finset.sum_apply, map_sum]

theorem free_quot [IsDomain O] [IsPrincipalIdealRing O] (s : A →+* O) (N : Submodule A (ι → A))
    (e : (ι → A) →ₗ[A] (ι → A)) (he1 : ∀ x, e x ∈ N) (he2 : ∀ x ∈ N, e x = x) :
    Module.Free O ((ι → O) ⧸ Submodule.span O ((fun r => s ∘ r) '' (N : Set (ι → A)))) := by
  set P := Submodule.span O ((fun r => s ∘ r) '' (N : Set (ι → A))) with hPdef
  have hfix : P ≤ LinearMap.ker (bcEnd s e - LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    simp [bcEnd_comp, he2 r hr]
  have hrange : ∀ y, bcEnd s e y ∈ P := by
    intro y
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨e (Pi.single k 1), he1 _, rfl⟩
  haveI : Module.IsTorsionFree O ((ι → O) ⧸ P) := Module.IsTorsionFree.of_smul_eq_zero fun c q h => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective P q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    rw [Submodule.Quotient.mk_eq_zero]
    have h1 := hfix h
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_smul] at h1
    have h2 : c • (bcEnd s e x - x) = 0 := h1
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hc
    · rw [← sub_eq_zero.1 h3]; exact hrange x
  exact Module.free_of_finite_type_torsion_free'

end GlobalTheory.FreeDedekindQuotient

noncomputable section
namespace GlobalTheory.FreeDedekindQuotient
open Formalism.BasicNotions NumberField

theorem exists_proj {A : Type} [CommRing A] [IsDedekindDomain A] {ι : Type} [Fintype ι]
    (N : Submodule A (ι → A)) (htf : ∀ a : A, a ≠ 0 → ∀ x, a • x ∈ N → x ∈ N) :
    ∃ e : (ι → A) →ₗ[A] (ι → A), (∀ x, e x ∈ N) ∧ ∀ x ∈ N, e x = x := by
  have htor : Submodule.torsion A ((ι → A) ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff q).1 hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at ha
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact htf a (nonZeroDivisors.coe_ne_zero a) x ha
  haveI : Module.Flat A ((ι → A) ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  haveI := Module.finitePresentation_of_finite A ((ι → A) ⧸ N)
  haveI : Module.Projective A ((ι → A) ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property N.mkQ LinearMap.id (Submodule.mkQ_surjective N)
  refine ⟨LinearMap.id - σ ∘ₗ N.mkQ, fun x => ?_, fun x hx => ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero]
    have := congrArg (fun f => f (N.mkQ x)) hσ
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]
    rw [← Submodule.mkQ_apply N (σ (N.mkQ x)), this, Submodule.mkQ_apply, sub_self]
  · have h0 : N.mkQ x = 0 := by simpa using hx
    simp [h0]

theorem dedekind_of_concrete (D : D7) (h : Function.Injective D.what₂.OtoLL ∧
    ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) :
    IsDedekindDomain D.what₂.O := by
  obtain ⟨hinj, F, hF⟩ := h
  have hc : Formalism.MainNotions.DIV.Inh.OsConcrete D := by
    refine ⟨hinj, F.toIntermediateField (fun x => by
      rw [eq_ratCast (algebraMap ℚ D.what₂.LL) x]; exact SubfieldClass.ratCast_mem F x), ?_⟩
    ext x
    have := hF x
    rw [RingHom.mem_range] at this
    exact this
  obtain ⟨K, _, _, ⟨e⟩⟩ := Formalism.MainNotions.DIV.Inh.OsRingOfIntegers_of_concrete D hc
  exact { e.symm.toMulEquiv.isDomain _, isNoetherianRing_of_ringEquiv _ e, Ring.DimensionLEOne.of_ringEquiv e.symm,
      IsIntegrallyClosed.of_equiv e with }

end GlobalTheory.FreeDedekindQuotient

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.BjFree

theorem latRel_torsionFree (D : D7) (hinj : Function.Injective D.what₂.OtoLL) (j : ℕ) (a : D.what₂.O) (ha : a ≠ 0)
    (x : (D.what₂.MjLat j).gen → D.what₂.O) (hx : a • x ∈ Formalism.L2.latRelSub (D.what₂.MjLat j)) :
    x ∈ Formalism.L2.latRelSub (D.what₂.MjLat j) := by
  simp only [Formalism.L2.mem_latRelSub, Formalism.L2.latRel, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, map_mul,
    mul_smul] at hx ⊢
  rw [← Finset.smul_sum] at hx
  have hne : (D.what₂.embLL.comp D.what₂.OtoLL) a ≠ 0 := by
    rw [RingHom.comp_apply]
    exact (_root_.map_ne_zero _).2 ((map_ne_zero_iff _ hinj).2 ha)
  exact (smul_eq_zero.1 hx).resolve_left hne


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem bjC_free : ∀ (D : D7) (B : LocBase0 D.host D.what₂) (hI : OsInt B), (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → ∀ i, Module.Free (OOf B i) (BjC B hI i) := by
  intro D B hI hO i
  classical
  haveI := GlobalTheory.FreeDedekindQuotient.dedekind_of_concrete D hO
  obtain ⟨e, he1, he2⟩ := GlobalTheory.FreeDedekindQuotient.exists_proj (Formalism.L2.latRelSub (D.what₂.MjLat (jOf B i)))
    (fun a ha x hx => latRel_torsionFree D hO.1 _ a ha x hx)
  haveI : IsPrincipalIdealRing (OOf B i) := inferInstance
  have hF := GlobalTheory.FreeDedekindQuotient.free_quot (sOfC B hI i) _ e he1 he2
  exact hF

end GlobalTheory.BjFree
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBaseChangeFreeOverLocalisationCoeffRingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeBaseChange_free_over_localisation_coeffRing : ∀ (D : D7) (B : LocBase0 D.host D.what₂) (hI : OsInt B), (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → ∀ i, Module.Free (OOf B i) (BjC B hI i) := by
  first | exact @GlobalTheory.BjFree.bjC_free | exact GlobalTheory.BjFree.bjC_free | (intros; apply GlobalTheory.BjFree.bjC_free <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStandardFactsOnLocalisationBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStandardFactsOnLocalisationBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeStdBase

theorem coeff_prod_isIntegral (m : Multiset ℂ) (hm : ∀ a ∈ m, IsIntegral ℤ a) (n : ℕ) :
    IsIntegral ℤ ((m.map fun a => X - C a).prod.coeff n) := by
  induction m using Multiset.induction_on generalizing n with
  | empty => simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one]; split_ifs <;> simp [isIntegral_one, isIntegral_zero]
  | cons a m ih =>
    have ha : IsIntegral ℤ a := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, IsIntegral ℤ b := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.map_cons, Multiset.prod_cons, coeff_mul]
    refine IsIntegral.sum _ fun x _ => IsIntegral.mul ?_ (ih hm' _)
    rw [coeff_sub, coeff_X, coeff_C]
    split_ifs <;> simp [isIntegral_one, isIntegral_zero, ha.neg, isIntegral_one.sub ha, ha]

theorem coeff_isIntegral_of_roots (Q : ℂ[X]) (hQ : Q.Monic) (c : ℕ) (h : ∀ a ∈ Q.roots, IsIntegral ℤ ((c : ℂ) * a)) (n : ℕ) :
    IsIntegral ℤ ((Q.scaleRoots (c : ℂ)).coeff n) := by
  have hs : Q = (Q.roots.map fun a => X - C a).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQ (IsAlgClosed.card_roots_eq_natDegree (k := ℂ))).symm
  have e : Q.scaleRoots (c : ℂ) = ((Q.roots.map fun a => a * (c : ℂ)).map fun a => X - C a).prod := by
    conv_lhs => rw [hs]
    clear hs
    induction Q.roots using Multiset.induction_on with
    | empty => simp
    | cons a m ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots,
        Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons]
  rw [e]
  refine coeff_prod_isIntegral _ (fun b hb => ?_) n
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
  rw [mul_comm]
  exact h a ha

end GlobalTheory.HeckeStdBase

namespace GlobalTheory.HeckeStdBase

theorem mem_range_of_roots {K : Type} [Field K] {O : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    {l : ℕ} (hl : l.Prime) (hu : ∀ d : ℕ, ¬ l ∣ d → IsUnit (d : O))
    (φ : K →+* ℂ) (ψ : K →+* FractionRing O) (p : K[X]) (hp : p.Monic)
    (hr : ∀ ρ : ℂ, (p.map φ).IsRoot ρ → ∃ d : ℕ, ¬ l ∣ d ∧ IsIntegral ℤ ((d : ℂ) * ρ))
    (μ : FractionRing O) (hμ : (p.map ψ).IsRoot μ) : μ ∈ (algebraMap O (FractionRing O)).range := by
  classical
  set Q := p.map φ with hQ
  have hQm : Q.Monic := hp.map φ
  let df : ℂ → ℕ := fun ρ => if h : Q.IsRoot ρ then (hr ρ h).choose else 1
  have hdf : ∀ ρ, ¬ l ∣ df ρ := by
    intro ρ
    simp only [df]
    split_ifs with h
    · exact (hr ρ h).choose_spec.1
    · exact Nat.Prime.not_dvd_one hl
  let c : ℕ := ∏ ρ ∈ Q.roots.toFinset, df ρ
  have hc : ¬ l ∣ c := by
    intro h
    obtain ⟨ρ, -, hρ⟩ := (Prime.dvd_finsetProd_iff hl.prime _).1 h
    exact hdf ρ hρ
  have hcr : ∀ a ∈ Q.roots, IsIntegral ℤ ((c : ℂ) * a) := by
    intro a ha
    have hroot : Q.IsRoot a := (mem_roots hQm.ne_zero).1 ha
    have hd : df a ∣ c := Finset.dvd_prod_of_mem _ (Multiset.mem_toFinset.2 ha)
    obtain ⟨e, he⟩ := hd
    have h1 : IsIntegral ℤ ((df a : ℂ) * a) := by
      simp only [df, dif_pos hroot]
      exact (hr a hroot).choose_spec.2
    have : (c : ℂ) * a = (e : ℂ) * ((df a : ℂ) * a) := by
      rw [show c = df a * e from he]; push_cast; ring
    rw [this]
    have he' : IsIntegral ℤ (e : ℂ) := by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (e : ℤ)))
    exact IsIntegral.mul he' h1

  have hK : ∀ n, IsIntegral ℤ ((p.scaleRoots (c : K)).coeff n) := by
    intro n
    have h1 := coeff_isIntegral_of_roots Q hQm c hcr n
    have e : (p.scaleRoots (c : K)).map φ = Q.scaleRoots (c : ℂ) := by
      rw [map_scaleRoots _ _ _ (by rw [hp.leadingCoeff, map_one]; exact one_ne_zero), map_natCast]
    rw [← e, coeff_map] at h1
    exact (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 h1
  have hO : ∀ n, ((p.scaleRoots (c : K)).map ψ).coeff n ∈ Set.range (algebraMap O (FractionRing O)) := by
    intro n
    rw [coeff_map]
    have h3 : IsIntegral O (ψ ((p.scaleRoots (c : K)).coeff n)) := by
      obtain ⟨q, hq, he⟩ := hK n
      refine ⟨q.map (Int.castRingHom O), hq.map _, ?_⟩
      rw [eval₂_map]
      have ec : (algebraMap O (FractionRing O)).comp (Int.castRingHom O) = ψ.comp (algebraMap ℤ K) := RingHom.ext_int _ _
      rw [ec, ← hom_eval₂, he, map_zero]
    exact IsIntegrallyClosed.isIntegral_iff.1 h3
  have hmon : ((p.scaleRoots (c : K)).map ψ).Monic := by
    refine Monic.map ψ ?_
    rw [Monic, leadingCoeff_scaleRoots, hp.leadingCoeff]
  obtain ⟨P0, hP0, -, hP0m⟩ := lifts_and_degree_eq_and_monic ((lifts_iff_coeff_lifts _).2 hO) hmon
  have hroot : eval₂ ψ (ψ (c : K) * μ) (p.scaleRoots (c : K)) = 0 := by
    refine scaleRoots_eval₂_eq_zero ψ ?_
    rw [eval₂_eq_eval_map]; exact hμ
  have hint : IsIntegral O (ψ (c : K) * μ) := by
    refine ⟨P0, hP0m, ?_⟩
    rw [eval₂_eq_eval_map, hP0, ← eval₂_eq_eval_map]
    rw [eval₂_eq_eval_map, ← eval₂_eq_eval_map (f := ψ)] at *
    exact hroot
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  obtain ⟨u, hu'⟩ := hu c hc
  refine ⟨(↑u⁻¹ : O) * z, ?_⟩
  rw [map_mul, hz, map_natCast, ← mul_assoc, ← map_natCast (algebraMap O (FractionRing O)) c, ← hu', ← map_mul,
    Units.inv_mul, map_one, one_mul]

end GlobalTheory.HeckeStdBase

namespace GlobalTheory.HeckeStdBase

theorem exists_complexify {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E] [Module.Finite K E]
    {F : Type} [AddCommGroup F] [Module ℂ F] [Module.Finite ℂ F] (φ : K →+* ℂ) (j : E →ₛₗ[φ] F)
    (hj : LinearIndependent ℂ (fun i => j (Module.Free.chooseBasis K E i)) ∧
      Submodule.span ℂ (Set.range fun i => j (Module.Free.chooseBasis K E i)) = ⊤)
    (T : Module.End K E) :
    ∃ (TC : Module.End ℂ F) (b' : Module.Basis (Module.Free.ChooseBasisIndex K E) ℂ F),
      (∀ i, b' i = j (Module.Free.chooseBasis K E i)) ∧ (∀ x, TC (j x) = j (T x)) ∧ TC.charpoly = T.charpoly.map φ := by
  classical
  set b := Module.Free.chooseBasis K E with hb
  let b' : Module.Basis (Module.Free.ChooseBasisIndex K E) ℂ F := Module.Basis.mk hj.1 hj.2.ge
  have hb' : ∀ i, b' i = j (b i) := fun i => Module.Basis.mk_apply _ _ _
  let TC : Module.End ℂ F := b'.constr ℂ (fun i => j (T (b i)))
  have hcomm : ∀ x, TC (j x) = j (T x) := by
    have e : (TC.comp j : E →ₛₗ[φ] F) = j.comp T := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply, TC, ← hb', Module.Basis.constr_basis]
    intro x
    exact congrArg (fun f : E →ₛₗ[φ] F => f x) e
  have hrepr : ∀ z i, b'.repr (j z) i = φ (b.repr z i) := by
    intro z i
    have e : j z = ∑ i, φ (b.repr z i) • b' i := by
      conv_lhs => rw [← b.sum_repr z]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, hb']
    rw [e, b'.repr_sum_self]
  refine ⟨TC, b', hb', hcomm, ?_⟩
  rw [← LinearMap.charpoly_toMatrix TC b', ← LinearMap.charpoly_toMatrix T b, ← Matrix.charpoly_map]
  congr 1
  ext i k
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hb', hcomm, hrepr]

end GlobalTheory.HeckeStdBase

namespace GlobalTheory.HeckeStdBase

section Gen

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}


set_option synthInstance.maxHeartbeats 400000 in
theorem isRoot_of_eig (B : LocBase0 H what₂) (j : ℕ) (w : what₂.places.Pl) (v : HeightOneSpectrum (𝓞 H.E)) (k : ℕ)
    [Module.Finite what₂.LL (what₂.MtL (what₂.muTw w) j)] (μ : FractionRing (B.Oc j w))
    (hμ : (B.hK j w v k).maxGenEigenspace μ ≠ ⊥) :
    ((B.hL j w v k).charpoly.map (B.ec j w)).IsRoot μ := by
  have hE : (B.hK j w v k).HasEigenvalue μ :=
    (Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one (by simp)).1 hμ
  obtain ⟨x, hx⟩ := hE.exists_hasEigenvector
  have hpow : ∀ (n : ℕ) (y : what₂.MtL (what₂.muTw w) j), (B.hK j w v k ^ n) (B.iV j w y) = B.iV j w ((B.hL j w v k ^ n) y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, B.hK_def, ih, pow_succ, Module.End.mul_apply]
  have e : ∀ (q : Polynomial what₂.LL) (y : what₂.MtL (what₂.muTw w) j),
      Polynomial.aeval (B.hK j w v k) (q.map (B.ec j w)) (B.iV j w y) = B.iV j w (Polynomial.aeval (B.hL j w v k) q y) := by
    intro q y
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq]
    | monomial n a =>
      simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
      rw [hpow, LinearMap.map_smulₛₗ]
  have hz : Polynomial.aeval (B.hK j w v k) ((B.hL j w v k).charpoly.map (B.ec j w)) = 0 := by
    have hb := (B.iV_basis j w (Module.Free.chooseBasis what₂.LL _)).2
    refine LinearMap.ext_on_range hb fun a => ?_
    rw [e, LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]
  have h0 := Module.End.aeval_apply_of_hasEigenvector (p := (B.hL j w v k).charpoly.map (B.ec j w)) hx
  rw [hz, LinearMap.zero_apply] at h0
  exact (smul_eq_zero.1 h0.symm).resolve_right hx.2

end Gen

end GlobalTheory.HeckeStdBase

namespace GlobalTheory.HeckeStdBase

theorem finite_MtL {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) : Module.Finite what₂.LL (what₂.MtL μ j) := by
  have h := (what₂.jMt_basis μ j (Module.Free.chooseBasis what₂.LL _)).1
  haveI : Finite (Module.Free.ChooseBasisIndex what₂.LL (what₂.MtL μ j)) := h.finite
  exact Module.Finite.of_basis (Module.Free.chooseBasis what₂.LL _)

variable {D : D7}


set_option synthInstance.maxHeartbeats 400000 in
theorem root_int (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (hP : HeckeStdPlain) (hG : GenHyp M C.Q)
    (hsp : ∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ)
    (j : ℕ) (w : D.what₂.places.Pl) (v : PlE D.host) (k : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hg : GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k) (ρ : ℂ)
    (hρ : (@LinearMap.charpoly D.what₂.LL _ _ _ _ (Module.Free.of_divisionRing _ _) (finite_MtL D.what₂ _ j)
      (hLC (mt0 M) C.Q hR j w v k)).map D.what₂.embLL |>.IsRoot ρ) :
    ∃ d : ℕ, ¬ D.what₂.places.resChar w ∣ d ∧ IsIntegral ℤ ((d : ℂ) * ρ) := by
  haveI := finite_MtL D.what₂ (D.what₂.muTw w) j
  obtain ⟨s, ϖ, hcj, hu⟩ := hsp v hg.1
  obtain ⟨Bs, hOut, hB⟩ := hG w j h1 h2
  have hsB : s.v ∉ Bs := hB v k s hg hcj
  obtain ⟨hmem, hlin, -, hint⟩ := hP D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ Bs (M (D.what₂.muTw w) j h1 h2).J_open hOut s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  obtain ⟨TC, b', hb', hcomm, hchar⟩ := exists_complexify D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) j)
    (D.what₂.jMt_basis _ _ _) (hLC (mt0 M) C.Q hR j w v k)
  have hev : TC.HasEigenvalue ρ := (Module.End.hasEigenvalue_iff_isRoot_charpoly TC ρ).2 (by rw [hchar]; exact hρ)
  obtain ⟨y, hy⟩ := hev.exists_hasEigenvector
  set Mr := M (D.what₂.muTw w) j h1 h2 with hMr
  have hin : ∀ z, Mr.real z ∈ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ := fun z => by
    rw [← Mr.real_range]; exact LinearMap.mem_range_self _ _
  have h0 : NG.tN Mr.J s ϖ k (0 : GAf D.host.E D.R.nV → Mr.wt.W) = 0 := by
    have := hlin 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) 1
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  let G : D.what₂.Mt (D.what₂.muTw w) j →ₗ[ℂ] (GAf D.host.E D.R.nV → Mr.wt.W) :=
    { toFun := fun z => NG.tN Mr.J s ϖ k (Mr.real z)
      map_add' := fun z z' => by
        have := hlin _ (hin z) _ (hin z') 1
        rw [one_smul] at this
        rw [map_add (f := _), this, one_smul]
      map_smul' := fun c z => by
        have := hlin _ (hin z) _ (Submodule.zero_mem _) c
        rw [add_zero, h0, add_zero] at this
        rw [map_smul, this]; rfl }
  have hreal : Mr.real ∘ₗ TC = G := by
    refine b'.ext fun i => ?_
    rw [LinearMap.comp_apply, hb', hcomm]
    exact hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hcj hu _
  have hf0 : Mr.real y ≠ 0 := fun h => hy.2 (Mr.real_inj (by rw [h, map_zero]))
  have hfe : NG.tN Mr.J s ϖ k (Mr.real y) = ρ • Mr.real y := by
    have e := congrArg (fun f => f y) hreal
    simp only [LinearMap.comp_apply] at e
    rw [hy.apply_eq_smul, map_smul] at e
    exact e.symm
  have hnab : ¬ s.Above (D.what₂.places.resChar w) := by
    intro hab
    have hw : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := by
      have := hab
      unfold SplitPlace.Above at this
      rw [← s.w_under, Ideal.mem_comap, map_natCast] at this
      exact this
    apply hg.2.1
    show ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal
    exact (hcj _ _ (by simp)).2 hw
  exact hint _ (hin y) hf0 ρ hfe _ (D.what₂.places.resChar_prime w) hnab

end GlobalTheory.HeckeStdBase

namespace GlobalTheory.HeckeStdBase


set_option synthInstance.maxHeartbeats 400000 in
theorem heckeStd0_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂)
    (hS : SplitK (mt0 M) C.Q hR X), HeckeStdPlain → GenHyp M C.Q →
    (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) →
    (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) →
    HeckeStd0 (base M C hR X hS) := by
  intro D M C hR X hS hP hG hsp hc j w h1 h2
  refine ⟨fun v k v' k' _ _ => ?_, fun v k hg μ hμ => ?_⟩
  · have hb := (iVC_basis X j w (Module.Free.chooseBasis D.what₂.LL _)).2
    refine LinearMap.ext_on_range hb fun a => ?_
    change (base M C hR X hS).hK j w v k ((base M C hR X hS).hK j w v' k' ((base M C hR X hS).iV j w _)) =
      (base M C hR X hS).hK j w v' k' ((base M C hR X hS).hK j w v k ((base M C hR X hS).iV j w _))
    rw [(base M C hR X hS).hK_def, (base M C hR X hS).hK_def, (base M C hR X hS).hK_def, (base M C hR X hS).hK_def,
      ← Module.End.mul_apply, ← Module.End.mul_apply]
    exact congrArg (fun f : Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) =>
      (base M C hR X hS).iV j w (f ((Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j)) a))) (hc j w v k v' k').eq
  haveI := finite_MtL D.what₂ (D.what₂.muTw w) j
  have hroot := isRoot_of_eig (base M C hR X hS) j w v k μ hμ
  have hu : ∀ d : ℕ, ¬ D.what₂.places.resChar w ∣ d → IsUnit (d : OcC X j w) := by
    intro d hd
    have h : IsUnit (d : ℤ_[D.what₂.places.resChar w]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd (D.what₂.places.resChar_prime w)).2 hd
    simpa using h.map (algebraMap ℤ_[D.what₂.places.resChar w] (OcC X j w))
  exact mem_range_of_roots (D.what₂.places.resChar_prime w) hu D.what₂.embLL (ecC X j w) _ (LinearMap.charpoly_monic _)
    (fun ρ hρ => root_int M C hR hP hG hsp j w v k h1 h2 hg ρ hρ) μ hroot

end GlobalTheory.HeckeStdBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStandardFactsOnLocalisationBaseStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStandardFacts_on_localisation_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) → HeckeStd0 (base M C hR X hS) := by
  first | exact @GlobalTheory.HeckeStdBase.heckeStd0_base | exact GlobalTheory.HeckeStdBase.heckeStd0_base | (intros; apply GlobalTheory.HeckeStdBase.heckeStd0_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBridgesAtPlacesOverResidueCharOfLargeCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBridgesAtPlacesOverResidueCharOfLargeCoeff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.BridgeAll

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem exists_finExt_ge {l : ℕ} [Fact l.Prime] {ι : Type} (S : Set ι) (hS : S.Finite) (L : ι → Loc.FinExt l) :
    ∃ F : Loc.FinExt l, ∀ i ∈ S, (L i).1 ≤ F.1 := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨⟨⊥, inferInstance⟩, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | @insert a s _ _ ih =>
    obtain ⟨F, hF⟩ := ih
    have h1 := F.2
    have h2 := (L a).2
    refine ⟨⟨(L a).1 ⊔ F.1, IntermediateField.finiteDimensional_sup _ _⟩, ?_⟩
    rintro i (rfl | hi)
    · exact le_sup_left
    · exact (hF i hi).trans le_sup_right

theorem placesOver_finite (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite := by
  have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem exists_bridge_good {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω]
    [IsAlgClosure H.E Ω] (u : HeightOneSpectrum (𝓞 H.E)) (A : ValuationSubring Ω) (hA : IsPlaceOver A u) :
    ∃ L0 : Loc.FinExt l, u ∈ placesOver H.E l → ∀ LL : Loc.FinExt l, L0.1 ≤ LL.1 →
      ∃ Bw : LocBridge l H.E Ω (Dec (F := H.E) A) ↥(Loc.OL LL),
        (∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) ∧ Loc.GoodCoef H.condN Bw.LL ∧
        ∀ x : ↥(Loc.OL LL), ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) = ((x : ↥LL.1) : Loc.Om l) := by
  by_cases hu : u ∈ placesOver H.E l
  · obtain ⟨j, L0, hj, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l H.E Ω u A hu hA
    let L1 : Loc.FinExt l := UpperTheory.KStar.Cyc.rootsExt l _ (UpperTheory.KStar.Cyc.lcm_ne_zero (l := l) H.toHostRaw)
    have f0 := L0.2
    have f1 := L1.2
    refine ⟨⟨L0.1 ⊔ L1.1, IntermediateField.finiteDimensional_sup _ _⟩, fun _ LL hLL => ?_⟩
    obtain ⟨Bw, e1, e2, e3, e4⟩ := hB LL (le_sup_left.trans hLL)
    refine ⟨Bw, by rw [e1]; exact hj, ?_, e4⟩
    rw [e2]
    exact UpperTheory.KStar.Cyc.mem_of_rootsExt_le _ (le_sup_right.trans hLL)
  · exact ⟨⟨⊥, inferInstance⟩, fun h => absurd h hu⟩

theorem brAt_of_large : ∀ (D : D7) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w),
    ∀ (X : CoefIn D.what₂) (j : ℕ), F0.1 ≤ (X.Kx j w).1 → BrAt X j w := by
  intro D w
  choose L hL using fun u : PlE D.host =>
    exists_bridge_good D.host (D.what₂.places.resChar w) D.nd.Om u (D.nd.plOm.1 u) (D.nd.plOm.2 u)
  obtain ⟨F, hF⟩ := exists_finExt_ge _ (placesOver_finite D.host.E (D.what₂.places.resChar_prime w)) L
  refine ⟨F, fun X j hX u hu => ?_⟩
  obtain ⟨Bw, h1, h2, h3⟩ := hL u hu (X.Kx j w) ((hF u hu).trans hX)
  exact ⟨Bw, h1, h2, fun z => (iqC_alg X j w z).trans (h3 z).symm⟩

end GlobalTheory.HeckeLocN.BridgeAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBridgesAtPlacesOverResidueCharOfLargeCoeffStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBridges_at_placesOverResidueChar_of_large_coeff : ∀ (D : D7) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), F0.1 ≤ (X.Kx j w).1 → BrAt X j w := by
  first | exact @GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large | exact GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large | (intros; apply GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingAllHeckeEigenvalue
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingAllHeckeEigenvalue
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeSplitField

open Module

theorem aeval_baseChange {L K M : Type} [Field L] [Field K] [Algebra L K] [AddCommGroup M] [Module L M]
    (f : Module.End L M) (p : L[X]) :
    aeval (f.baseChange K) (p.map (algebraMap L K)) = (aeval f p).baseChange K := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [Polynomial.map_add (f := _), map_add (f := _), hp, hr, map_add (f := _), LinearMap.baseChange_add]
  | monomial k c =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← LinearMap.baseChange_pow]
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x
    simp [Module.algebraMap_end_apply, LinearMap.baseChange_tmul]

theorem iSup_maxGen_baseChange {L K M I : Type} [Field L] [Field K] [Algebra L K] [AddCommGroup M] [Module L M]
    [FiniteDimensional L M] (op : I → Module.End L M) (hc : ∀ x y, Commute (op x) (op y)) {p : L[X]}
    (hp : Formalism.L2.Col.HeckePolyFor op p) (hsp : (p.map (algebraMap L K)).Splits) (x : I) :
    ⨆ μ, Module.End.maxGenEigenspace ((op x).baseChange K) μ = ⊤ := by
  classical
  obtain ⟨hp0, s, hs, hd⟩ := hp
  obtain ⟨c, hcx⟩ := hs x
  have e : (op x).baseChange K = ∑ y ∈ s, algebraMap L K (c y) • (op y).baseChange K := by
    rw [hcx]
    change LinearMap.baseChangeHom L K M M (∑ y ∈ s, c y • op y) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    change (c y • op y).baseChange K = _
    rw [LinearMap.baseChange_smul, algebraMap_smul]
  rw [e]
  refine Formalism.L2.Col.hfs_iSup_maxGen_sum s (fun y => (op y).baseChange K) (fun y => algebraMap L K (c y))
    (fun y _ z _ => ?_) (fun y hy => ?_)
  · change _ * _ = _ * _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, (hc y z).eq]
  · apply Formalism.L2.Col.hfs_iSup_maxGen_of_splits
    refine hsp.of_dvd (Polynomial.map_ne_zero hp0) (minpoly.dvd K _ ?_)
    rw [aeval_baseChange, hd y hy, LinearMap.baseChange_zero]

theorem finiteDimensional_mtL {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) :
    FiniteDimensional what₂.LL (what₂.MtL μ j) := by
  let b := Module.Free.chooseBasis what₂.LL (what₂.MtL μ j)
  haveI : Finite (Module.Free.ChooseBasisIndex what₂.LL (what₂.MtL μ j)) := ((what₂.jMt_basis μ j b).1).finite
  exact Module.Finite.of_basis b

end GlobalTheory.HeckeSplitField

namespace GlobalTheory.HeckeSplitField

open Module

theorem exists_finExt_split : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (E0 : PlEmb D.what₂),
    (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) →
    ∀ (j : ℕ) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ X : CoefIn D.what₂, X.E = E0 →
      F0.1 ≤ (X.Kx j w).1 → ∀ v k, GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k →
        ⨆ μ, (hKC (mt0 M) C.Q hR X j w v k).maxGenEigenspace μ = ⊤ := by
  intro D M C hR E0 hcomm j w
  classical
  haveI : FiniteDimensional D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := finiteDimensional_mtL D.what₂ _ j
  let op : HeightOneSpectrum (𝓞 D.host.E) × ℕ → Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) :=
    fun vk => hLC (mt0 M) C.Q hR j w vk.1 vk.2
  obtain ⟨p, hp⟩ := Formalism.L2.Col.hfs_exists_poly op
  let S : Set (PadicAlgCl (D.what₂.places.resChar w)) := ((p.map (E0.emb w)).roots.toFinset : Set _)
  haveI : Finite S := Finset.finite_toSet _
  have hfin : FiniteDimensional ℚ_[D.what₂.places.resChar w] (IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨⟨IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] S, hfin⟩, ?_⟩
  intro X hXE hF v k _
  have hmap : (p.map (ecC X j w)).map (iqC X j w) = p.map (E0.emb w) := by
    rw [Polynomial.map_map]
    congr 1
    ext x
    rw [RingHom.comp_apply, iqC_ec, hXE]
  have hsp : (p.map (algebraMap D.what₂.LL (FractionRing (OcC X j w)))).Splits := by
    refine Polynomial.Splits.of_splits_map (iqC X j w) ?_ fun a ha => ?_
    · change ((p.map (ecC X j w)).map (iqC X j w)).Splits
      rw [hmap]
      exact IsAlgClosed.splits _
    · change a ∈ ((p.map (ecC X j w)).map (iqC X j w)).roots at ha
      rw [hmap] at ha
      have haS : a ∈ S := by
        simp only [S, Finset.coe_sort_coe, Finset.mem_coe, Multiset.mem_toFinset]
        exact ha
      exact iqC_surj X j w a (hF (IntermediateField.subset_adjoin _ _ haS))
  exact iSup_maxGen_baseChange op (fun x y => hcomm j w x.1 x.2 y.1 y.2) hp hsp (v, k)

end GlobalTheory.HeckeSplitField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingAllHeckeEigenvalueStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicFiniteExt_containing_all_hecke_eigenvalues : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (E0 : PlEmb D.what₂), (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) → ∀ (j : ℕ) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ X : CoefIn D.what₂, X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∀ v k, GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k → ⨆ μ, (hKC (mt0 M) C.Q hR X j w v k).maxGenEigenspace μ = ⊤ := by
  first | exact @GlobalTheory.HeckeSplitField.exists_finExt_split | exact GlobalTheory.HeckeSplitField.exists_finExt_split | (intros; apply GlobalTheory.HeckeSplitField.exists_finExt_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigenspaceNeBotEveryLocalisationPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigenspaceNeBotEveryLocalisationPoint
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.EigOcc

open Module Module.End

section Lin

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem inf_ker_ne_bot {a : End K V} {c : K} {U : Submodule K V} (hU : U ≠ ⊥)
    (hle : U ≤ a.maxGenEigenspace c) (hinv : ∀ y ∈ U, a y ∈ U) :
    U ⊓ LinearMap.ker (a - c • 1) ≠ ⊥ := by
  classical
  obtain ⟨y, hyU, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have hy := hle hyU
  rw [mem_maxGenEigenspace] at hy
  have hP : ∃ n : ℕ, ((a - c • (1 : End K V)) ^ n) y = 0 := hy
  have hm : ((a - c • 1) ^ Nat.find hP) y = 0 := Nat.find_spec hP
  have hm0 : Nat.find hP ≠ 0 := by
    intro h
    rw [h, pow_zero, Module.End.one_apply] at hm
    exact hy0 hm
  obtain ⟨m', hm'⟩ : ∃ m', Nat.find hP = m' + 1 := ⟨Nat.find hP - 1, by omega⟩
  have hne : ((a - c • 1) ^ m') y ≠ 0 := Nat.find_min hP (by omega)
  have hinv' : ∀ k : ℕ, ((a - c • 1) ^ k) y ∈ U := by
    intro k
    induction k with
    | zero => simpa using hyU
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact U.sub_mem (hinv _ ih) (U.smul_mem c ih)
  intro hbot
  apply hne
  have hmem : ((a - c • 1) ^ m') y ∈ U ⊓ LinearMap.ker (a - c • 1) := by
    refine ⟨hinv' m', ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ', ← hm']
    exact hm
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).1 hmem

theorem exists_common_eigvec (S : Set (End K V)) (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (χ : End K V → K)
    (W0 : Submodule K V) (hW : W0 ≠ ⊥) (hle : ∀ a ∈ S, W0 ≤ a.maxGenEigenspace (χ a))
    (hinv : ∀ a ∈ S, ∀ y ∈ W0, a y ∈ W0) :
    ∃ u ∈ W0, u ≠ 0 ∧ ∀ a ∈ S, a u = χ a • u := by
  classical
  have hP : ∃ n, ∃ U : Submodule K V, U ≤ W0 ∧ U ≠ ⊥ ∧ (∀ a ∈ S, ∀ y ∈ U, a y ∈ U) ∧ finrank K U = n :=
    ⟨_, W0, le_rfl, hW, hinv, rfl⟩
  obtain ⟨U, hUW, hU0, hUinv, hUn⟩ := Nat.find_spec hP
  have key : ∀ a ∈ S, U ≤ LinearMap.ker (a - χ a • 1) := by
    intro a ha
    have hU'0 : U ⊓ LinearMap.ker (a - χ a • 1) ≠ ⊥ := inf_ker_ne_bot hU0 (hUW.trans (hle a ha)) (hUinv a ha)
    have hU'inv : ∀ b ∈ S, ∀ y ∈ U ⊓ LinearMap.ker (a - χ a • 1), b y ∈ U ⊓ LinearMap.ker (a - χ a • 1) := by
      rintro b hb y ⟨hyU, hyk⟩
      refine ⟨hUinv b hb y hyU, ?_⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker] at hyk
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      have hc : Commute (a - χ a • 1) b := (hS a ha b hb).sub_left ((Commute.one_left b).smul_left _)
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hyk, map_zero]
    have hle' : finrank K U ≤ finrank K ↥(U ⊓ LinearMap.ker (a - χ a • 1)) := by
      rw [hUn]
      exact Nat.find_min' hP ⟨_, inf_le_left.trans hUW, hU'0, hU'inv, rfl⟩
    have heq : U ⊓ LinearMap.ker (a - χ a • 1) = U := Submodule.eq_of_le_of_finrank_le inf_le_left hle'
    rw [← heq]
    exact inf_le_right
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  refine ⟨u, hUW huU, hu0, fun a ha => ?_⟩
  have h := key a ha huU
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
  exact h

end Lin

end GlobalTheory.EigOcc

namespace GlobalTheory.EigOcc

theorem mem_heckeEig_of_gen {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (x : X) (G : Set (X → O))
    (hT : T = Algebra.adjoin O G) (z : TensorProduct O (FractionRing O) M)
    (hG : ∀ f : T, (f : X → O) ∈ G →
      ((act f).baseChange (FractionRing O)) z = algebraMap O (FractionRing O) ((f : X → O) x) • z) :
    z ∈ heckeEig T act x := by
  rw [heckeEig, Submodule.mem_iInf]
  intro f
  rw [Module.End.mem_eigenspace_iff]
  obtain ⟨g, hgT⟩ := f
  have hg : g ∈ Algebra.adjoin O G := hT ▸ hgT
  induction hg using Algebra.adjoin_induction with
  | mem g hg' => exact hG ⟨g, hgT⟩ hg'
  | algebraMap r =>
    have e1 : (⟨algebraMap O (X → O) r, hgT⟩ : T) = algebraMap O T r := rfl
    rw [e1, AlgHom.commutes, Algebra.algebraMap_eq_smul_one r, LinearMap.baseChange_smul, LinearMap.baseChange_one,
      LinearMap.smul_apply, Module.End.one_apply, ← algebraMap_smul (FractionRing O) r z]
    rfl
  | add g1 g2 h1 h2 ih1 ih2 =>
    have m1 : g1 ∈ T := hT ▸ h1
    have m2 : g2 ∈ T := hT ▸ h2
    have e1 : (⟨g1 + g2, hgT⟩ : T) = ⟨g1, m1⟩ + ⟨g2, m2⟩ := rfl
    rw [e1, map_add (f := _), LinearMap.baseChange_add, LinearMap.add_apply, ih1 m1, ih2 m2]
    simp only [Subalgebra.coe_add, Pi.add_apply, map_add (f := _), add_smul]
  | mul g1 g2 h1 h2 ih1 ih2 =>
    have m1 : g1 ∈ T := hT ▸ h1
    have m2 : g2 ∈ T := hT ▸ h2
    have e1 : (⟨g1 * g2, hgT⟩ : T) = ⟨g1, m1⟩ * ⟨g2, m2⟩ := rfl
    rw [e1, map_mul, LinearMap.baseChange_mul, Module.End.mul_apply, ih2 m2, LinearMap.map_smul, ih1 m1, smul_smul]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, map_mul, mul_comm]

end GlobalTheory.EigOcc

namespace GlobalTheory.EigOcc

section Main

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}


set_option maxHeartbeats 1000000 in
theorem heckeEig_ne_bot (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd))
    (hAct : ActEx B (partCompl_of hs hd)) (hH : ActHK B hs hd hL hAct) (i : LocT B) (x : XOf B i) :
    heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x ≠ ⊥ := by
  classical
  haveI := hd (jOf B i) (wOf B i)
  let S : Set (Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i))) :=
    {f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = B.hK (jOf B i) (wOf B i) v k}
  let χ : Module.End (FractionRing (OOf B i)) (B.V (jOf B i) (wOf B i)) → FractionRing (OOf B i) :=
    fun a => if h : a ∈ hAlg B i then NCov.pt x.1 ⟨a, h⟩ else 0
  have hSc : ∀ a ∈ S, ∀ b ∈ S, Commute a b := std_comm (j := jOf B i) (w := wOf B i) hs i.2.2.2.1 i.2.2.2.2.1
  have hmem : ∀ a ∈ S, a ∈ hAlg B i := fun a ha => Algebra.subset_adjoin ha
  have hχ : ∀ a (ha : a ∈ S), χ a = NCov.pt x.1 ⟨a, hmem a ha⟩ := fun a ha => dif_pos (hmem a ha)
  obtain ⟨u, huW, hu0, hu⟩ := exists_common_eigvec S hSc χ (NCov.W (hAlg B i) (NCov.pt x.1)) x.2.2
    (fun a ha => by
      rw [hχ a ha]
      exact NCov.W_le (hAlg B i) (NCov.pt x.1) ⟨a, hmem a ha⟩)
    (fun a ha y hy => by
      rw [NCov.W, Submodule.mem_iInf] at hy ⊢
      intro t
      exact Module.End.mapsTo_maxGenEigenspace_of_comm (NCov.commute_adjoin hSc t.2 (hmem a ha)) _ (hy t))
  have hpart : u ∈ NCov.part (hAlg B i) i.2.1 :=
    (le_iSup₂ (f := fun (ψ : hAlg B i →ₐ[OOf B i] OOf B i) (_ : NCov.cls ψ = i.2.1) => NCov.W (hAlg B i) (NCov.pt ψ))
      x.1 x.2.1) huW
  obtain ⟨z, hz⟩ := (PsiC_range B (partCompl_of hs hd) hL i u).1 hpart
  have hG : ∀ f : TOf B i, (f : XOf B i → OOf B i) ∈ {f | ∃ v k, GenAt0 H (lOf B i) (B.Qw (wOf B i)) v k ∧ f = hTfun B i v k} →
      ((actC B (partCompl_of hs hd) hAct i f).baseChange (FractionRing (OOf B i))) z =
        algebraMap (OOf B i) (FractionRing (OOf B i)) ((f : XOf B i → OOf B i) x) • z := by
    rintro f ⟨v, k, hvk, hf⟩
    have e1 : f = hTOf B i v k := Subtype.ext (by rw [hf]; simp [hTOf, dif_pos hvk])
    subst e1
    apply PsiC_inj B (partCompl_of hs hd) hL i
    rw [hH i v k hvk z, hz, map_smul, hz, hu _ ⟨v, k, hvk, rfl⟩, hχ _ ⟨v, k, hvk, rfl⟩]
    exact congrArg (· • u) (congrArg (algebraMap (OOf B i) (FractionRing (OOf B i))) (ptX_val B i v k hvk x).symm)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact hu0 hz.symm
  intro hbot
  apply hz0
  have hzm : z ∈ heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x :=
    mem_heckeEig_of_gen (TOf B i) (actC B (partCompl_of hs hd) hAct i) x _ rfl z hG
  rw [hbot] at hzm
  exact (Submodule.mem_bot _).1 hzm

end Main

end GlobalTheory.EigOcc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigenspaceNeBotEveryLocalisationPointStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEigenspace_ne_bot_every_localisation_point : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd)), ActHK B hs hd hL hAct → ∀ (i : LocT B) (x : XOf B i), heckeEig (TOf B i) (actC B (partCompl_of hs hd) hAct i) x ≠ ⊥ := by
  first | exact @GlobalTheory.EigOcc.heckeEig_ne_bot | exact GlobalTheory.EigOcc.heckeEig_ne_bot | (intros; apply GlobalTheory.EigOcc.heckeEig_ne_bot <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocN

set_option synthInstance.maxHeartbeats 400000

def feSup {l : ℕ} [Fact l.Prime] (K L : Loc.FinExt l) : Loc.FinExt l :=
  ⟨K.1 ⊔ L.1, haveI := K.2; haveI := L.2; IntermediateField.finiteDimensional_sup _ _⟩

theorem osInt (D : D7) (B : LocBase0 D.host D.what₂) : OsInt B := fun j w y =>
  IsIntegrallyClosed.isIntegral_iff.1 <| by
    obtain ⟨p, hp, h0⟩ := D.O_int y
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [eval₂_map, Subsingleton.elim (RingHom.comp _ _) ((B.ec j w).comp (algebraMap ℤ D.what₂.LL)), ← hom_eval₂, h0, map_zero]

theorem plGwDisj (D : D7) : PlGwDisj D := by
  have key : ∀ v v', D.naut.plGw 0 v ≠ D.naut.plGw 1 v' := fun v v' e => by
    have h0 : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw 0 v).asIdeal := D.naut.plGw_over 0 v
    have h1 : ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw 1 v').asIdeal := D.naut.plGw_over 1 v'
    rw [← e] at h1
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
      ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne).cast
    exact (D.naut.plGw 0 v).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)))
  intro k k' v v' e
  fin_cases k <;> fin_cases k'
  · rfl
  · exact absurd e (key v v')
  · exact absurd e.symm (key v' v)
  · rfl

section Psi

variable {D : D7} {C : NChoice D} {X : CoefIn D.what₂} {ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)}
  (hψ0 : ∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) =
    algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w))))
  (hP : PsiInt X ψ0) (j : ℕ) (w : D.what₂.places.Pl)

theorem psN_spec (g : G D.host.E D.nd.Om) : algebraMap (OcC X j w) (FractionRing (OcC X j w)) (psN X ψ0 hP j w g : OcC X j w) =
    ecC X j w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
  unitsLift_spec ((Units.map (ecC X j w).toMonoidHom).comp (ψ0 w)) (hP j w) g


include hψ0 in
theorem psN_eq_one (g : G D.host.E D.nd.Om) : psN X ψ0 hP j w g = 1 ↔ ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) g = 1 := by
  rw [← Units.val_eq_one, ← map_eq_one_iff _ (IsFractionRing.injective (OcC X j w) (FractionRing (OcC X j w))), psN_spec,
    map_eq_one_iff _ (ecC X j w).injective, ← map_eq_one_iff _ (C.embW w).injective, hψ0,
    map_eq_one_iff _ (IsFractionRing.injective (C.Oe w) (FractionRing (C.Oe w))), map_eq_one_iff _ (C.Oe_inj w),
    Units.val_eq_one]
  rfl

include hψ0 in
theorem psN_of_art {g : G D.host.E D.nd.Om} (h : D.ntw.art (C.twI w) (C.Q w) g = 1) : psN X ψ0 hP j w g = 1 := by
  rw [psN_eq_one hψ0, MonoidHom.comp_apply, h, map_one]

include hψ0 in
theorem psN_ord (g : G D.host.E D.nd.Om) : ∃ n : ℕ, psN X ψ0 hP j w g ^ (D.what₂.places.resChar w ^ n) = 1 := by
  obtain ⟨n, hn⟩ := D.ntw.RCG_l _ _ (D.ntw.art (C.twI w) (C.Q w) g)
  rw [C.twI_l, ← map_pow] at hn
  exact ⟨n, by rw [← map_pow]; exact psN_of_art hψ0 hP j w hn⟩

include hψ0 in
theorem psN_open : IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om)) :=
  Subgroup.isOpen_mono (H₁ := (D.ntw.art (C.twI w) (C.Q w)).ker) (fun _ hg => psN_of_art hψ0 hP j w hg) (D.ntw.art_cont _ _)

include hψ0 in
theorem psN_anti : AntiHom D.ntw.cc (psN X ψ0 hP j w) := fun g g' h => by
  rw [eq_inv_iff_mul_eq_one, ← map_mul]
  exact psN_of_art hψ0 hP j w (by rw [map_mul, D.ntw.art_anti _ _ g g' h, inv_mul_cancel])

include hψ0 in
theorem psN_ram (h : ∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) :
    RamExactly (psN X ψ0 hP j w) (↑(C.Q w) : Set (HeightOneSpectrum (𝓞 D.host.E))) := fun v A hA => by
  constructor
  · rintro ⟨σ, hσ, hne⟩
    by_contra hv
    exact hne (psN_of_art hψ0 hP j w (D.ntw.art_unr _ _ v hv A hA σ hσ))
  · intro hv
    obtain ⟨σ, hσ, hne⟩ := h v hv A hA
    exact ⟨σ, hσ, fun e => hne ((psN_eq_one hψ0 hP j w σ).1 e)⟩

end Psi


end GlobalTheory.HeckeLocN
