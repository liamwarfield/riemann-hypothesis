module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsJumpMultiset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit
noncomputable section

namespace GlobalTheory.DeRhamSplit

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem finrank_split [inst : Fintype (K →ₐ[Qp] LL)]
    (hcard : Fintype.card (K →ₐ[Qp] LL) = Module.finrank Qp K)
    (ρ : Representation LL G V) [Module.Finite LL (DdR PD ρ)] :
    Module.finrank LL (DdR PD ρ) = ∑ τ : K →ₐ[Qp] LL, Module.finrank LL (DdRE PD ρ τ) ∧
      ∀ a : ℤ, Module.finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
        ∑ τ : K →ₐ[Qp] LL, Module.finrank LL (FildR PD ρ τ a) := by
  haveI := PD.finK
  obtain rfl : inst = minpoly.AlgHom.fintype Qp K LL := Subsingleton.elim _ _
  have hm : ∀ (c : K) (v : V) (b : BdR),
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ b) = v ⊗ₜ (algebraMap K BdR c * b) :=
    fun _ _ _ => rfl
  let m : K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) :=
    { toFun := fun c => mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c
      map_one' := by ext v b; simp [hm]
      map_mul' := fun c d => by ext v b; simp [hm, mul_assoc]
      map_zero' := by ext v b; simp [hm]
      map_add' := fun c d => by ext v b; simp [hm, add_mul, tmul_add]
      commutes' := fun r => by
        ext v b
        simp [hm, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] }
  have hD : ∀ x, x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hc : ∀ g c x, actVdR PD ρ g (m c x) = m c (actVdR PD ρ g x) := by
    intro g c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [m, hm, actVdR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hst : ∀ c, ∀ x ∈ DdR PD ρ, m c x ∈ DdR PD ρ := fun c x hx =>
    (hD _).2 fun g => by rw [hc, (hD x).1 hx g]
  have hF : ∀ a c, ∀ x ∈ FilV PD (LL := LL) (V := V) a, m c x ∈ FilV PD (LL := LL) (V := V) a := by
    rintro a c _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      refine ⟨v ⊗ₜ ⟨c • (b : BdR), (PD.Fil a).smul_mem c b.2⟩, ?_⟩
      change v ⊗ₜ (c • (b : BdR)) = v ⊗ₜ (algebraMap K BdR c * (b : BdR))
      rw [Algebra.smul_def]
    | add y z hy hz => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hy hz
  have hE : ∀ (τ : K →ₐ[Qp] LL) x, x ∈ DdRE PD ρ τ ↔ x ∈ DdR PD ρ ∧ ∀ c, m c x = τ c • x := fun τ x => by
    simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  haveI : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL (DdRE PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  refine ⟨GlobalTheory.Cmp.JumpDict.finrank_eq_sum_emb hcard m (DdR PD ρ) hst (DdRE PD ρ) hE, fun a => ?_⟩
  haveI : ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL (FildR PD ρ τ a) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := DdRE PD ρ τ) inf_le_left
  refine GlobalTheory.Cmp.JumpDict.finrank_eq_sum_emb hcard m (DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)
    (fun c x hx => ⟨hst c x hx.1, hF a c x hx.2⟩)
    (fun τ => FildR PD ρ τ a) fun τ x => ?_
  simp only [FildR, Submodule.mem_inf, hE]
  tauto

end General

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)], Splits (Qp := ℚ_[l]) (K := ↥K.1) ↥LL.1 → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), Module.Finite ↥LL.1 ↥(DdR (P.PD K) ρ) → Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = ∑ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ ∀ a : ℤ, Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a) = ∑ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Module.finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ a) := by
  intro l _ P K LL _ hs V _ _ _ _ ρ hfin
  exact finrank_split (P.PD K) hs.2 ρ

end GlobalTheory.DeRhamSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCharactersTypePrimeProof
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContChiRat
noncomputable section

namespace GlobalTheory.HfCharProof

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
  (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem act_chiRat (c : ℕ) (g : Br.G D.nbr i w hw) (x : Fin 1 → Br.LL D.nbr i w hw) :
    matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c)) g x =
      (D.nbr i w hw).toLL (((chiU D.nd i c * (chiU D.nd i 1)⁻¹)
        (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) • x := by
  funext b
  rw [Subsingleton.elim b 0]
  change (Br.loc D.nbr i w hw (chiRatO D.nd i c) g).mulVec x 0 = _
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Fin.isValue, Pi.smul_apply, smul_eq_mul]
  congr 1
  change (D.nbr i w hw).toLL (chiRatO D.nd i c (decS D.nd w (Br.iota D.nbr i w hw g)) 0 0) = _
  congr 1
  simp [chiRatO, twistM]

theorem cont_chiRat (c : ℕ) (x : Fin 1 → Br.LL D.nbr i w hw) :
    Continuous fun g => matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c)) g x := by
  simp only [act_chiRat]
  have hs : Continuous fun g : Br.G D.nbr i w hw => decS D.nd w (Br.iota D.nbr i w hw g) :=
    continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw)
  have hL : Continuous (D.nbr i w hw).toLL := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h1 : Continuous fun g : Br.G D.nbr i w hw => (D.nbr i w hw).toLL
      ((D.nd.chi i c (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      (D.nbr i w hw).toLL
      ((D.nd.chi i 1 (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) : (D.nd.O i)ˣ) : D.nd.O i) :=
    (hL.comp ((D.nd.chi_cont i c).comp hs)).mul
      (hL.comp ((D.nd.chi_cont i 1).comp (hs.comp continuous_inv)))
  refine Continuous.smul (h1.congr fun g => ?_) continuous_const
  rw [← map_mul, ← Units.val_mul, map_inv, map_inv, map_inv]
  rfl

theorem chiRat_eq (n : ℕ) (hn : n = 0 ∨ n + 1 ≤ D.R.t) (g : Formalism.MainNotions.N.GE D.nd) :
    (chiU D.nd i (n + 1) * (chiU D.nd i 1)⁻¹) g = (epsU D.nd i g)⁻¹ ^ n := by
  rcases hn with rfl | hc
  · simp
  · have h := D.nd.chi_def i (n + 1) (by omega) hc
    change D.nd.chi i (n + 1) g * (D.nd.chi i 1)⁻¹ g = _
    rw [mul_comm, h, MonoidHom.mul_apply, MonoidHom.inv_apply, inv_mul_cancel_left, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, MonoidHom.zpow_apply, zpow_neg, zpow_natCast, inv_pow]
    rfl

theorem eps_eq (g : Br.G D.nbr i w hw) :
    (D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) =
      algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]) := by
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  rw [Br.PD, (D.loc _).PD_χ, ← GlobalTheory.BlockJumps.cycZ_eq_chi (D.nbr i w hw) (D.loc _) g]
  exact congrArg Subtype.val ((D.nbr i w hw).eO_alg _)

theorem act_eq (n : ℕ) (hn : n = 0 ∨ n + 1 ≤ D.R.t) (g : Br.G D.nbr i w hw)
    (x : Fin 1 → Br.LL D.nbr i w hw) :
    matRep (Br.loc D.nbr i w hw (chiRatO D.nd i (n + 1))) g x =
      ((algebraMap ℚ_[D.nd.l i] (Br.LL D.nbr i w hw)
        ((Br.PD D.loc D.nbr i w hw).χ g : ℚ_[D.nd.l i]))⁻¹) ^ n • x := by
  rw [act_chiRat, chiRat_eq D i n hn, Units.val_pow_eq_pow_val, map_pow, map_units_inv, eps_eq]

def chiLat (c : ℕ) :
    LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw) where
  V := Fin 1 → Br.LL D.nbr i w hw
  ρ := matRep (Br.loc D.nbr i w hw (chiRatO D.nd i c))
  cont := cont_chiRat D i w hw c
  L := Br.locLat D.nbr i w hw (chiRatO D.nd i c)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem hfChar : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LocalSituation.Conclusion4 D HW F → InertEq D →
    ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      D.nd.l i ≠ 2 → (D.nbr i w hw).Kw.1 ≤ Ks (D.nbr i w hw).Kw 1 → HfChar i w hw := by
  intro D HW F h4 hI i w hw h2 hK
  have hs := (D.self_good i w hw).good_one (D.nbr i w hw).LL_split h2 hK
  have hT := (h4 (D.nd.l i) _ 1 _ hs).2
  have hr : ∀ c, finrank (Br.LL D.nbr i w hw) (chiLat D i w hw c).V = 1 := fun c =>
    Module.finrank_fin_fun _
  refine ⟨fun c hc => ?_, fun f hf => ?_⟩
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    obtain ⟨n, rfl⟩ : ∃ n, c = n + 1 := ⟨c - 1, by omega⟩
    exact ((hT n (chiLat D i w hw (n + 1)) (hr _) (act_eq D i w hw n (Or.inr hc2))).2.1 (by omega)).le
  · obtain ⟨-, x, hx⟩ :=
      ((hT 0 (chiLat D i w hw 1) (hr _) (act_eq D i w hw 0 (Or.inl rfl))).2.2 rfl f).1 hf
    refine ⟨x, fun g hg => hx g ?_⟩
    rw [hI i w hw] at hg
    exact hg

end GlobalTheory.HfCharProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCharactersTypePrimeProof
noncomputable section

namespace GlobalTheory.Pass.HfCharStep

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem main : StepHfChar := fun D _ HW F h hI i _ _ h2 w hw h1 =>
  GlobalTheory.HfCharProof.hfChar D HW F h hI i w hw h2 ((IntermediateField.finrank_eq_one_iff.mp h1).le.trans bot_le)

end GlobalTheory.Pass.HfCharStep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCharactersTypePrimeProofStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoCharactersTypePrime_proof : StepHfChar := by
  first | exact @GlobalTheory.Pass.HfCharStep.main | exact GlobalTheory.Pass.HfCharStep.main | (intros; apply GlobalTheory.Pass.HfCharStep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegree
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.UnrDeg

theorem det_pow_ne_zero {k F : Type} [Field k] [Field F] [Algebra k F] (τ : F ≃ₐ[k] F) {n : ℕ}
    (hord : orderOf τ = n) (bas : Module.Basis (Fin n) k F) :
    (Matrix.of fun i j : Fin n => (τ ^ (j : ℕ)) (bas i)).det ≠ 0 := by
  intro h
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  let L : F →ₗ[k] F :=
    { toFun := fun x => ∑ j : Fin n, u j * (τ ^ (j : ℕ)) x
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_smul_comm]
        congr 1
        exact (τ ^ (j : ℕ)).toLinearEquiv.map_smul r x }
  have hL : L = 0 := by
    refine bas.ext fun i => ?_
    have := congrFun hu i
    simpa [L, Matrix.mulVec, dotProduct, mul_comm] using this
  let f : Fin n → (F →* F) := fun j => ((τ ^ (j : ℕ)).toRingEquiv : F ≃+* F).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    have hi : (i : ℕ) ∈ Set.Iio (orderOf τ) := by rw [hord]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf τ) := by rw [hord]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h1)
  have li := (linearIndependent_monoidHom F F).comp f hf
  rw [Fintype.linearIndependent_iff] at li
  apply hu0
  funext j
  refine li u ?_ j
  funext x
  have := LinearMap.congr_fun hL x
  simpa [L, f, Finset.sum_apply, smul_eq_mul] using this

variable {l : ℕ} [Fact l.Prime]

def sig (l : ℕ) [Fact l.Prime] : ↥(MaximalUnramifiedExtension l) ≃ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  AlgEquiv.ofBijective (frobUr l) frobUr_bijective

theorem fr_apply (k : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : fr l k c = (frobUr l ^ k) c := rfl

theorem sig_pow (k : ℕ) (c : ↥(MaximalUnramifiedExtension l)) : (sig l ^ k) c = fr l k c := by
  rw [fr_apply]
  induction k generalizing c with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgHom.mul_apply, ih]; rfl

end GlobalTheory.PMon.UnrDeg

namespace GlobalTheory.PMon.UnrDeg

theorem exists_moved (l : ℕ) [hl : Fact l.Prime] {r k : ℕ} (hk0 : 0 < k) (hkr : k < r) :
    ∃ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ∧ fr l k c ≠ c := by
  have h2 := hl.out.two_le
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hls : l ^ k ≤ l ^ s := Nat.pow_le_pow_right (by omega) (by omega)
  have hl1 : l ^ 1 ≤ l ^ k := Nat.pow_le_pow_right (by omega) hk0
  rw [pow_one] at hl1
  have h5 : l ^ s * 2 ≤ l ^ s * l := Nat.mul_le_mul_left _ h2
  have hps : l ^ (s + 1) = l ^ s * l := pow_succ _ _
  have hN0 : 0 < l ^ (s + 1) - 1 := by omega
  have hkN : l ^ k < l ^ (s + 1) - 1 := by omega
  have h1N : 1 < l ^ (s + 1) - 1 := by omega
  have hd : ¬ l ∣ l ^ (s + 1) - 1 := fun h => hl.out.one_lt.ne' (Nat.dvd_one.mp
    ((Nat.dvd_sub_iff_right (by omega) (dvd_pow_self l (by omega))).mp h))
  haveI : NeZero (l ^ (s + 1) - 1) := ⟨hN0.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ (s + 1) - 1)
  have hmem : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, hN0, hd, hz.pow_eq_one⟩
  have h1 : (⟨z, hmem⟩ : ↥(MaximalUnramifiedExtension l)) ^ (l ^ (s + 1) - 1) = 1 := Subtype.ext hz.pow_eq_one
  refine ⟨⟨z, hmem⟩, ?_, fun h => ?_⟩
  · rw [fr_apply, frobUr_pow_root _ _ _ hN0 hd h1, show l ^ (s + 1) = (l ^ (s + 1) - 1) + 1 by omega, pow_succ, h1,
      one_mul]
  · rw [fr_apply, frobUr_pow_root _ _ _ hN0 hd h1] at h
    have h6 : z ^ l ^ k = z ^ 1 := by rw [pow_one]; exact congrArg Subtype.val h
    have := hz.pow_inj hkN h1N h6
    omega

theorem fixed_field_deg : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (E : FinExt l) (ω : Fin r → ↥(MaximalUnramifiedExtension l)),
    E.1 ≤ MaximalUnramifiedExtension l ∧ Module.finrank ℚ_[l] ↥E.1 = r ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ↔ (c : Om l) ∈ E.1) ∧
    (∀ k, fr l r (ω k) = ω k) ∧ LinearIndependent ℚ_[l] ω ∧
    (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) ∧
    (Matrix.of fun m k : Fin r => fr l m (ω k)).det ≠ 0 := by
  intro l _ r hr
  let σ := sig l
  let F : IntermediateField ℚ_[l] ↥(MaximalUnramifiedExtension l) := IntermediateField.fixedField (Subgroup.zpowers (σ ^ r))
  have hF : ∀ c, c ∈ F ↔ fr l r c = c := fun c => by
    rw [IntermediateField.mem_fixedField_iff, ← sig_pow]
    refine ⟨fun h => h _ (Subgroup.mem_zpowers _), fun h f hf => ?_⟩
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer _ c)).2 h hf
  have hst : ∀ c ∈ F, σ c ∈ F := fun c hc => by
    rw [hF, ← sig_pow] at hc ⊢
    rw [← AlgEquiv.mul_apply, ← pow_succ, pow_succ', AlgEquiv.mul_apply, hc]
  let τ₀ : ↥F →ₐ[ℚ_[l]] ↥F := ((σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l)).comp F.val).codRestrict F.toSubalgebra
    fun c => hst c c.2
  let τ : ↥F ≃ₐ[ℚ_[l]] ↥F := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact AlgEquiv.ofBijective τ₀ (Algebra.IsAlgebraic.algHom_bijective _)
  have hτ : ∀ (k : ℕ) (c : ↥F), (((τ ^ k) c : ↥F) : ↥(MaximalUnramifiedExtension l)) = fr l k c := fun k c => by
    rw [← sig_pow]
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← ih]; rfl
  have hrτ : τ ^ r = 1 := AlgEquiv.ext fun c => Subtype.ext ((hτ r c).trans ((hF c).1 c.2))
  have hord : orderOf τ = r := by
    rw [orderOf_eq_iff hr]
    refine ⟨hrτ, fun k hkr hk0 hk => ?_⟩
    obtain ⟨c, hc, hm⟩ := exists_moved l hk0 hkr
    have := hτ k ⟨c, (hF c).2 hc⟩
    rw [hk, AlgEquiv.one_apply] at this
    exact hm this.symm
  have hfin : IsOfFinOrder τ := isOfFinOrder_iff_pow_eq_one.2 ⟨r, hr, hrτ⟩
  haveI : Finite ↥(Subgroup.zpowers τ) := hfin.finite_zpowers
  have hbot : IntermediateField.fixedField (Subgroup.zpowers τ) = ⊥ := by
    rw [eq_bot_iff]
    intro c hc
    rw [IntermediateField.mem_fixedField_iff] at hc
    have h1 := congrArg Subtype.val (hc τ (Subgroup.mem_zpowers _))
    have h2 := hτ 1 c
    rw [pow_one] at h2
    obtain ⟨x, hx⟩ := (GlobalTheory.MemLoc.frob_laws l (frobUr l) frobUr_root).2.2 c (h2.symm.trans h1)
    exact ⟨x, Subtype.ext hx⟩
  haveI h1 : FiniteDimensional ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F :=
    inferInstanceAs (FiniteDimensional ↥(FixedPoints.subfield (Subgroup.zpowers τ) ↥F) ↥F)
  haveI h2 : FiniteDimensional ℚ_[l] ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) := by
    rw [hbot]; infer_instance
  haveI h3 : FiniteDimensional ℚ_[l] ↥F := Module.Finite.trans ↥(IntermediateField.fixedField (Subgroup.zpowers τ)) ↥F
  have hdeg : Module.finrank ℚ_[l] ↥F = r := by
    have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers τ)
    rw [hbot, IntermediateField.finrank_bot', Nat.card_zpowers] at h
    exact h.trans hord
  let bas : Module.Basis (Fin r) ℚ_[l] ↥F := Module.finBasisOfFinrankEq ℚ_[l] ↥F hdeg
  refine ⟨⟨F.map (MaximalUnramifiedExtension l).val, (F.equivMap (MaximalUnramifiedExtension l).val).toLinearEquiv.finiteDimensional⟩, fun k => (bas k : ↥(MaximalUnramifiedExtension l)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro x ⟨y, -, rfl⟩
    exact y.2
  · show Module.finrank ℚ_[l] ↥(F.map (MaximalUnramifiedExtension l).val) = r
    rw [← (F.equivMap (MaximalUnramifiedExtension l).val).toLinearEquiv.finrank_eq]
    exact hdeg
  · intro c
    show _ ↔ (c : Om l) ∈ F.map (MaximalUnramifiedExtension l).val
    rw [IntermediateField.mem_map, ← hF]
    refine ⟨fun h => ⟨c, h, rfl⟩, ?_⟩
    rintro ⟨y, hy, hyc⟩
    rwa [← Subtype.ext hyc]
  · intro k
    exact (hF _).1 (bas k).2
  · exact bas.linearIndependent.map' F.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · intro c hc
    refine ⟨bas.repr ⟨c, (hF c).2 hc⟩, ?_⟩
    have e := congrArg (F.val.toLinearMap) (bas.sum_repr ⟨c, (hF c).2 hc⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e
    simpa using e.symm
  · intro h0
    let M : Matrix (Fin r) (Fin r) ↥F := Matrix.of fun i j : Fin r => (τ ^ (j : ℕ)) (bas i)
    have e : (Matrix.of fun m k : Fin r => fr l m (bas k : ↥(MaximalUnramifiedExtension l))) = (F.val.mapMatrix M).transpose := by
      refine Matrix.ext fun m k => ?_
      simp only [M, Matrix.of_apply, Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
      exact (hτ m (bas k)).symm
    rw [e, Matrix.det_transpose, ← AlgHom.map_det] at h0
    exact det_pow_ne_zero τ hord bas (Subtype.ext h0)

end GlobalTheory.PMon.UnrDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedExtFixedFieldFrobeniusPowDegreeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedExt_fixedField_frobeniusPow_degree : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∃ (E : FinExt l) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), E.1 ≤ MaximalUnramifiedExtension l ∧ Module.finrank ℚ_[l] ↥E.1 = r ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c ↔ (c : Om l) ∈ E.1) ∧ (∀ k, fr l r (ω k) = ω k) ∧ LinearIndependent ℚ_[l] ω ∧ (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) ∧ (Matrix.of fun m k : Fin r => fr l m (ω k)).det ≠ 0 := by
  first | exact @GlobalTheory.PMon.UnrDeg.fixed_field_deg | exact GlobalTheory.PMon.UnrDeg.fixed_field_deg | (intros; apply GlobalTheory.PMon.UnrDeg.fixed_field_deg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImage
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImage
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.BlockCharpoly

open Polynomial

theorem exists_factor_of_idempotent {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K)
    (he : e * e = e) (hr : e.rank = t) :
    ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e := by
  classical
  set V := LinearMap.range e.mulVecLin with hV
  have hd : Module.finrank K V = t := hr
  let bs := Module.finBasisOfFinrankEq K V hd
  let P : (Fin n → K) →ₗ[K] V := e.mulVecLin.rangeRestrict
  let fa : (Fin t → K) →ₗ[K] (Fin n → K) := V.subtype ∘ₗ bs.equivFun.symm.toLinearMap
  let fb : (Fin n → K) →ₗ[K] (Fin t → K) := bs.equivFun.toLinearMap ∘ₗ P

  have hP : ∀ v : V, P v = v := by
    rintro ⟨v, w, rfl⟩
    apply Subtype.ext
    show e.mulVecLin (e.mulVecLin w) = e.mulVecLin w
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, he]
  refine ⟨LinearMap.toMatrix' fa, LinearMap.toMatrix' fb, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [fa, fb, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, hP,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · rw [← LinearMap.toMatrix'_comp]
    have hc : fa ∘ₗ fb = Matrix.toLin' e := by
      refine LinearMap.ext fun x => ?_
      simp only [fa, fb, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
        Submodule.coe_subtype, P, Matrix.toLin'_apply]
      rfl
    rw [hc, LinearMap.toMatrix'_toLin']

theorem blockPol_factor {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (hba : b * a = 1) (M : Matrix (Fin n) (Fin n) K) :
    blockPol (a * b) (a * b * M * (a * b)) = (b * M * a).charpoly := by
  unfold blockPol
  set A := a.map (C : K →+* K[X]) with hA
  set B := b.map (C : K →+* K[X]) with hB
  have hBA : B * A = 1 := by
    rw [hA, hB, ← Matrix.map_mul, hba, Matrix.map_one _ C.map_zero C.map_one]

  have hmat : (X : K[X]) • (a * b).map (C : K →+* K[X]) - (a * b * M * (a * b)).map (C : K →+* K[X])
        + 1 - (a * b).map (C : K →+* K[X])
      = 1 + (A * ((X : K[X]) • (1 : Matrix (Fin t) (Fin t) K[X]) - B * M.map (C : K →+* K[X]) * A - 1)) * B := by
    simp only [Matrix.map_mul, ← hA, ← hB, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hmat, Matrix.det_one_add_mul_comm, ← Matrix.mul_assoc, hBA, Matrix.one_mul, add_sub_cancel]
  have hBMA : B * M.map (C : K →+* K[X]) * A = (b * M * a).map (C : K →+* K[X]) := by
    rw [hA, hB, Matrix.map_mul, Matrix.map_mul]
  rw [hBMA, Matrix.charpoly]
  congr 1
  ext i j
  simp only [Matrix.charmatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp

theorem blockPol_eq_charpoly {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K)
    (he : e * e = e) (hr : e.rank = t) :
    ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e ∧
      ∀ M : Matrix (Fin n) (Fin n) K, blockPol e (e * M * e) = (b * M * a).charpoly := by
  obtain ⟨a, b, hba, hab⟩ := exists_factor_of_idempotent e he hr
  refine ⟨a, b, hba, hab, fun M => ?_⟩
  subst hab
  exact blockPol_factor a b hba M

end GlobalTheory.BlockCharpoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentBlockCharPolyEqCharpolyImageStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentBlockCharPoly_eq_charpoly_image : ∀ {K : Type} [Field K] {n t : ℕ} (e : Matrix (Fin n) (Fin n) K), e * e = e → e.rank = t → ∃ (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), b * a = 1 ∧ a * b = e ∧ ∀ M : Matrix (Fin n) (Fin n) K, blockPol e (e * M * e) = (b * M * a).charpoly := by
  first | exact @GlobalTheory.BlockCharpoly.blockPol_eq_charpoly | exact GlobalTheory.BlockCharpoly.blockPol_eq_charpoly | (intros; apply GlobalTheory.BlockCharpoly.blockPol_eq_charpoly <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJump
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJump
noncomputable section

namespace GlobalTheory.CycPow

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL]

theorem step (u : F) (hu : PD.ι PD.t * u = 1) (hu' : u ∈ PD.Fil (-1)) (n : ℤ) :
    finrank LL ↥(DdR PD (charRep (cycLL PD LL ^ (n + 1)))) =
        finrank LL ↥(DdR PD (charRep (cycLL PD LL ^ n))) ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ (n + 1))) τ (a - 1)) =
        finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ n)) τ a) := by
  have htw : IsTwistRep (cycLL PD LL) (charRep (cycLL PD LL ^ n)) (charRep (cycLL PD LL ^ (n + 1))) := by
    refine ⟨LinearEquiv.refl LL LL, fun g x => ?_⟩
    rw [zpow_add_one]
    change (((cycLL PD LL ^ n) g * cycLL PD LL g : LLˣ) : LL) * x =
      ((cycLL PD LL g : LLˣ) : LL) * ((((cycLL PD LL ^ n) g : LLˣ) : LL) * x)
    rw [Units.val_mul]
    ring
  obtain ⟨Φ, hD, hF⟩ := GlobalTheory.DRFil.exists_twist_equiv PD _ _ htw u hu hu'
  exact ⟨by rw [← hD, LinearEquiv.finrank_map_eq], fun τ a => by rw [← hF, LinearEquiv.finrank_map_eq]⟩

theorem isDR_and_finrank [CharZero Qp] [FiniteDimensional Qp LL] (u : F) (hu : PD.ι PD.t * u = 1)
    (hu' : u ∈ PD.Fil (-1)) (k : ℤ) :
    IsDR PD (charRep (cycLL PD LL ^ k)) ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ k)) τ a) = if a ≤ -k then 1 else 0 := by
  induction k using Int.induction_on with
  | zero =>
    have h1 : charRep (1 : G →* LLˣ) = Representation.trivial LL G LL := by
      ext g
      simp [charRep]
    rw [zpow_zero, h1, neg_zero]
    exact ⟨GlobalTheory.CrysExt.isDR_trivial PD, GlobalTheory.CrysExt.finrank_fildR_trivial PD⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := step PD (LL := LL) u hu hu' n
    refine ⟨h1.trans ih.1, fun τ a => ?_⟩
    have h3 := h2 τ (a + 1)
    rw [add_sub_cancel_right] at h3
    rw [h3, ih.2]
    exact if_congr (by omega) rfl rfl
  | pred n ih =>
    obtain ⟨h1, h2⟩ := step PD (LL := LL) u hu hu' (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h1 h2
    refine ⟨h1.symm.trans ih.1, fun τ a => ?_⟩
    rw [← h2, ih.2]
    exact if_congr (by omega) rfl rfl

end Generic

theorem cyc_zpow_crys_dR_jump : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (k : ℤ), IsCrys (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ IsDR (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) τ a = if a = -k then 1 else 0 := by
  intro l _ P AI T K LL k
  have := LL.2
  obtain ⟨u, hu', hu⟩ := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 K (-1) 1).1
    (by rw [neg_add_cancel]; exact (P.PD K).one_mem)
  have ht : (P.PD K).ι (P.PD K).t * u = 1 := by
    rw [P.PD_ι, P.period_datum_t_eq]
    exact hu.symm
  obtain ⟨h1, h2⟩ := isDR_and_finrank (P.PD K) (LL := ↥LL.1) u ht hu' k
  refine ⟨GlobalTheory.BlockCrys.isCrys_cyc_zpow _ k, h1, fun τ a => ?_⟩
  rw [multV, h2, h2]
  split_ifs <;> first | rfl | omega

end GlobalTheory.CycPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJumpStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyc_zpow_crys_dR_jump_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (k : ℤ), IsCrys (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ IsDR (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) τ a = if a = -k then 1 else 0 := by
  first | exact @GlobalTheory.CycPow.cyc_zpow_crys_dR_jump | exact GlobalTheory.CycPow.cyc_zpow_crys_dR_jump | (intros; apply GlobalTheory.CycPow.cyc_zpow_crys_dR_jump <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK

def frobSlice {K : Type} [Field K] (l i : ℕ) (z : K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun n => coeff (l * n + i) z

theorem coeff_frobSlice {K : Type} [Field K] (l i : ℕ) (z : K⟦X⟧) (n : ℕ) :
    coeff n (frobSlice l i z) = coeff (l * n + i) z := by
  simp [frobSlice]

namespace Hom

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

def rdivSet (F : Hom P Q) (τ : ZMod a) : Set K⟦X⟧ :=
  {h | (∃ c : ℝ, ∀ n, ‖coeff n h‖ ≤ c) ∧ ∃ Y : Matrix ι κ K⟦X⟧,
    (∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) ∧ F.mat τ * Y = h • (1 : Matrix κ κ K⟦X⟧)}

def ldivSet (F : Hom P Q) (τ : ZMod a) : Set K⟦X⟧ :=
  {h | (∃ c : ℝ, ∀ n, ‖coeff n h‖ ≤ c) ∧ ∃ Y : Matrix ι κ K⟦X⟧,
    (∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) ∧ Y * F.mat τ = h • (1 : Matrix ι ι K⟦X⟧)}

theorem bdd_mul {f g : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) (hg : ∃ c : ℝ, ∀ n, ‖coeff n g‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (f * g)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  exact ⟨a * b, fun n => by
    simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) ha0 hb0
      (f := f) (g := g) (by simpa using ha) (by simpa using hb) n⟩

theorem bdd_add {f g : K⟦X⟧} (hf : ∃ c : ℝ, ∀ n, ‖coeff n f‖ ≤ c) (hg : ∃ c : ℝ, ∀ n, ‖coeff n g‖ ≤ c) :
    ∃ c : ℝ, ∀ n, ‖coeff n (f + g)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨max a b, fun n => by
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (ha n) (hb n))⟩

theorem bdd_smul_matrix {μ ν : Type} {b : K⟦X⟧} {Y : Matrix μ ν K⟦X⟧} (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c)
    (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c) : ∃ c : ℝ, ∀ i j n, ‖coeff n ((b • Y) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hb
  obtain ⟨c, hc⟩ := hY
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  refine ⟨a * max c 0, fun i j n => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul]
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp) ha0
    (le_max_right c 0) (f := b) (g := Y i j) (by simpa using ha)
    (fun m => by rw [mul_one]; exact (hc i j m).trans (le_max_left _ _)) n

theorem rdivSet_add (F : Hom P Q) (τ : ZMod a) {x y : K⟦X⟧} (hx : x ∈ F.rdivSet τ) (hy : y ∈ F.rdivSet τ) :
    x + y ∈ F.rdivSet τ := by
  obtain ⟨hxb, Y₁, ⟨c₁, hc₁⟩, h₁⟩ := hx
  obtain ⟨hyb, Y₂, ⟨c₂, hc₂⟩, h₂⟩ := hy
  refine ⟨bdd_add hxb hyb, Y₁ + Y₂, ⟨max c₁ c₂, fun i j n => ?_⟩, ?_⟩
  · rw [Matrix.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hc₁ i j n) (hc₂ i j n))
  · rw [Matrix.mul_add, h₁, h₂, add_smul]

theorem ldivSet_add (F : Hom P Q) (τ : ZMod a) {x y : K⟦X⟧} (hx : x ∈ F.ldivSet τ) (hy : y ∈ F.ldivSet τ) :
    x + y ∈ F.ldivSet τ := by
  obtain ⟨hxb, Y₁, ⟨c₁, hc₁⟩, h₁⟩ := hx
  obtain ⟨hyb, Y₂, ⟨c₂, hc₂⟩, h₂⟩ := hy
  refine ⟨bdd_add hxb hyb, Y₁ + Y₂, ⟨max c₁ c₂, fun i j n => ?_⟩, ?_⟩
  · rw [Matrix.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hc₁ i j n) (hc₂ i j n))
  · rw [Matrix.add_mul, h₁, h₂, add_smul]

theorem rdivSet_mul (F : Hom P Q) (τ : ZMod a) {x : K⟦X⟧} (hx : x ∈ F.rdivSet τ) (b : K⟦X⟧)
    (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) : b * x ∈ F.rdivSet τ := by
  obtain ⟨hxb, Y, hY, h⟩ := hx
  refine ⟨bdd_mul hb hxb, b • Y, bdd_smul_matrix hb hY, ?_⟩
  rw [Matrix.mul_smul, h, smul_smul]

theorem ldivSet_mul (F : Hom P Q) (τ : ZMod a) {x : K⟦X⟧} (hx : x ∈ F.ldivSet τ) (b : K⟦X⟧)
    (hb : ∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) : b * x ∈ F.ldivSet τ := by
  obtain ⟨hxb, Y, hY, h⟩ := hx
  refine ⟨bdd_mul hb hxb, b • Y, bdd_smul_matrix hb hY, ?_⟩
  rw [Matrix.smul_mul, h, smul_smul]

end Hom

end GlobalTheory.BK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvrExtensionForMonicFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvrExtensionForMonicFamily
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

open Polynomial

theorem isLocalRing_of_domain_finite_padicInt (l : ℕ) [Fact l.Prime] (B : Type) [CommRing B]
    [IsDomain B] [Algebra ℤ_[l] B] [Module.Finite ℤ_[l] B] : IsLocalRing B := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun b => ?_
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h0, h1⟩ := hcon
  obtain ⟨E, hE, hM⟩ := GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem l b
  have e0 : E - 0 ∈ (Ideal.span {b}).restrictScalars ℤ_[l] := hM _ 0 fun n => by
    simp only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    exact dvd_pow_self b (Nat.succ_ne_zero n)
  have e1 : E - 1 ∈ (Ideal.span {1 - b}).restrictScalars ℤ_[l] := hM _ 1 fun n => by
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    have := one_sub_dvd_one_sub_pow b (n + 1)
    rw [← neg_sub 1 (b ^ (n + 1))]
    exact this.neg_right
  simp only [sub_zero, Submodule.restrictScalars_mem, Ideal.mem_span_singleton] at e0 e1
  rcases (IsIdempotentElem.iff_eq_zero_or_one (p := E)).1 hE with h | h
  · rw [h, zero_sub] at e1
    exact h1 (isUnit_of_dvd_one (dvd_neg.1 e1))
  · rw [h] at e0
    exact h0 (isUnit_of_dvd_one e0)

theorem exists_fin_prod_of_splits {L : Type} [Field L] (t : ℕ) (f : L[X]) (hs : f.Splits)
    (hm : f.Monic) (ht : f.natDegree = t) : ∃ α : Fin t → L, f = ∏ c, (X - C (α c)) := by
  have hc : f.roots.toList.length = t := by
    rw [Multiset.length_toList, ← hs.natDegree_eq_card_roots, ht]
  subst hc
  refine ⟨f.roots.toList.get, ?_⟩
  conv_lhs => rw [hs.eq_prod_roots_of_monic hm, ← Multiset.coe_toList f.roots]
  rw [Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
  congr 1
  conv_lhs => rw [← List.ofFn_get f.roots.toList]
  rw [List.map_ofFn]
  rfl

theorem exists_finite_dvr_splitting : ∀ (l : ℕ) [Fact l.Prime] {A ι : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] [Finite ι] (t : ℕ) (P : ι → Polynomial A), (∀ i, ((P i).map (toFr A)).Monic ∧ ((P i).map (toFr A)).natDegree = t) → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B), Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧ ∀ i, ∃ α : Fin t → FractionRing B, (P i).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) := by
  intro l _ A ι _ _ _ _ _ _ _ t P hP
  classical
  haveI := Fintype.ofFinite ι
  let K := FractionRing A
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing A
  let F : K[X] := ∏ i, (P i).map (toFr A)
  have hF : F.Monic := monic_prod_of_monic _ _ fun i _ => (hP i).1
  let L := F.SplittingField
  haveI : IsScalarTower A K L := inferInstance
  let S := integralClosure A L
  haveI : Module.Finite A S := IsIntegralClosure.finite A K L S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain A K L S
  haveI : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension A K L S
  haveI : IsLocalRing S := by
    letI : Algebra ℤ_[l] S := ((algebraMap A S).comp (algebraMap ℤ_[l] A)).toAlgebra
    haveI : IsScalarTower ℤ_[l] A S := .of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℤ_[l] S := Module.Finite.trans A S
    exact isLocalRing_of_domain_finite_padicInt l S
  have hinj : Function.Injective (algebraMap A S) :=
    algebraMap_injective_of_field_isFractionRing A S K L
  have hnf : ¬ IsField S := fun h =>
    IsDiscreteValuationRing.not_isField A (isField_of_isIntegral_of_isField hinj h)
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 3 1).1
    (inferInstance : IsDedekindDomain S)
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hinj,
    fun i => ?_⟩
  let e : L ≃ₐ[S] FractionRing S := (FractionRing.algEquiv S L).symm
  have hsF : (F.map (algebraMap K L)).Splits := SplittingField.splits F
  have hsi : (((P i).map (toFr A)).map (algebraMap K L)).Splits :=
    hsF.of_dvd (hF.map _).ne_zero
      (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  have hcomp : (toFr S).comp (algebraMap A S) =
      ((e : L →+* FractionRing S).comp (algebraMap K L)).comp (toFr A) := by
    ext a
    have : algebraMap K L (toFr A a) = algebraMap S L (algebraMap A S a) := by
      rw [← IsScalarTower.algebraMap_apply A S L]
      exact (IsScalarTower.algebraMap_apply A K L a).symm
    simp only [RingHom.comp_apply, this]
    exact (e.commutes _).symm
  rw [hcomp, ← Polynomial.map_map, ← Polynomial.map_map]
  refine exists_fin_prod_of_splits t _ (hsi.map _) (((hP i).1.map _).map _) ?_
  rw [natDegree_map, natDegree_map, (hP i).2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDvrExtensionForMonicFamilyStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_extension_for_monic_family : ∀ (l : ℕ) [Fact l.Prime] {A ι : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] [Finite ι] (t : ℕ) (P : ι → Polynomial A), (∀ i, ((P i).map (toFr A)).Monic ∧ ((P i).map (toFr A)).natDegree = t) → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B), Module.Finite A B ∧ Function.Injective (algebraMap A B) ∧ ∀ i, ∃ α : Fin t → FractionRing B, (P i).map ((toFr B).comp (algebraMap A B)) = ∏ c, (Polynomial.X - Polynomial.C (α c)) := by
  first | exact @GlobalTheory.exists_finite_dvr_splitting | exact GlobalTheory.exists_finite_dvr_splitting | (intros; apply GlobalTheory.exists_finite_dvr_splitting <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkFrobOfAttached
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal.HkFrobProof

theorem eval_charpolyRev_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b
  by_cases h : a = b <;> simp [h] <;> ring

theorem coeff_charpolyRev_map {n : ℕ} {R : Type} [CommRing R] (f : R →+* ℂ) (M : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    f (M.charpolyRev.coeff k) = (M.map f).charpolyRev.coeff k := by
  rw [← Polynomial.coeff_map]
  apply congrArg (fun p : ℂ[X] => p.coeff k)
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 1
  by_cases h : a = b <;> simp [h]

theorem charpolyRev_smul_inv {n : ℕ} (M A : Matrix (Fin n) (Fin n) ℂ) (h : M * A = 1) (β : Multiset ℂ)
    (hβ : (0 : ℂ) ∉ β) (hA : A.charpoly = (β.map fun a => (X : ℂ[X]) - C a).prod) (c : ℂ) :
    (c • M).charpolyRev = (β.map fun a => (1 : ℂ[X]) - C (c * a⁻¹) * X).prod := by
  have ev : ∀ y : ℂ, (y • (1 : Matrix (Fin n) (Fin n) ℂ) - A).det = (β.map fun a => y - a).prod := by
    intro y
    have := congrArg (Polynomial.eval y) hA
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal] at this
    simpa using this
  apply Polynomial.funext
  intro z
  rw [eval_charpolyRev_eq, eval_multiset_prod, Multiset.map_map]
  have h0 := ev 0
  have h1 := ev (z * c)
  have hne : (β.map fun a => (0 : ℂ) - a).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hm
    obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.1 hm
    have : a = 0 := by simpa using ha0
    exact hβ (this ▸ ha)
  apply mul_right_cancel₀ hne
  rw [← Multiset.prod_map_mul]
  conv_lhs => rw [← h0, ← Matrix.det_mul]
  have e : (1 - z • c • M) * ((0 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - A) = (z * c) • 1 - A := by
    rw [zero_smul, zero_sub, mul_neg, sub_mul, one_mul, smul_smul, Matrix.smul_mul, h, neg_sub]
  rw [e, h1]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  have ha0 : a ≠ 0 := fun h => hβ (h ▸ ha)
  simp only [Function.comp, eval_sub, eval_one, eval_mul, eval_C, eval_X]
  field_simp
  ring

theorem rd_injective {D : D7} (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) :
    Function.Injective (rd i ι) :=
  ι.injective.comp (IsFractionRing.injective (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)))

end GlobalTheory.TripleGal.HkFrobProof
end
