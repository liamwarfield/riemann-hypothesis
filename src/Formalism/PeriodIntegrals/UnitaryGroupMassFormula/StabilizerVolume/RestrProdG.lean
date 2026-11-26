module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdSt

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdG
noncomputable section

namespace PI.VolStabS.RestrProdG

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Maps

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S]

theorem map_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ z) =
      sigR S σ (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

theorem map_inclR (f : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR, Algebra.TensorProduct.map_tmul]

theorem map_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (x y : Fin n) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (gramR R σ J X x y) =
      gramR S σ J (fun x i => Algebra.TensorProduct.map f (AlgHom.id F E) (X x i)) x y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, map_sigR,
    map_inclR]

end Maps

theorem t2_tensor_product {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type)
    [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    T2Space (R ⊗[F] E) := by
  let b := Module.finBasis F E
  refine T2Space.of_injective_continuous
    (f := fun y : R ⊗[F] E => fun k => PositiveNearLattice.crd b R y k) ?_
    (continuous_pi fun k => PositiveNearLattice.continuous_crd b R k)
  intro y y' h
  have h' : ∀ k, PositiveNearLattice.crd b R y k = PositiveNearLattice.crd b R y' k := fun k => congrFun h k
  rw [PositiveNearLattice.eq_sum_crd b R y, PositiveNearLattice.eq_sum_crd b R y']
  simp only [h']

theorem rpGram_holds : RPGram := by
  intro F E _ _ _ _ _ σ M J a T
  let b := Module.finBasis F E
  refine ⟨?_, ?_, fun v => ?_, ?_⟩
  · have : T2Space (AF F ⊗[F] E) := t2_tensor_product (AF F)
    have : T2Space (Matrix (Fin a) (Fin a) (AF F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → AF F ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (AF F) σ J)).isOpen_compl.measurableSet
  · have : T2Space (Ainf F ⊗[F] E) := t2_tensor_product (Ainf F)
    have : T2Space (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Ainf F ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (Ainf F) σ J)).measurableSet
  · have : LocallyCompactSpace (Fv F v) := locallyCompact_Fv F v
    have : T2Space (Fv F v ⊗[F] E) := t2_tensor_product (Fv F v)
    have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (Fv F v) σ J)).measurableSet
  · intro X hI hV
    have key : ∀ w w' : AF F ⊗[F] E,
        Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) w =
          Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) w' →
        (∀ v, Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
            (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w) =
          Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
            (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w')) → w = w' := by
      intro w w' h1 h2
      rw [PositiveNearLattice.eq_sum_crd b (AF F) w, PositiveNearLattice.eq_sum_crd b (AF F) w']
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      have e1 := congrArg (fun u => PositiveNearLattice.crd b (Ainf F) u k) h1
      simp only [PositiveNearLattice.crd_map] at e1
      refine Prod.ext e1 (FiniteAdeleRing.ext (K := F) fun v => ?_)
      have e2 := congrArg (fun u => PositiveNearLattice.crd b (Fv F v) u k) (h2 v)
      simp only [PositiveNearLattice.crd_map] at e2
      exact e2
    funext x y
    refine key _ _ ?_ fun v => ?_
    · rw [map_gramR, Matrix.map_apply, map_inclR]
      exact congrFun (congrFun hI x) y
    · rw [map_gramR, map_gramR, Matrix.map_apply, map_inclR, map_inclR]
      exact congrFun (congrFun (hV v) x) y

end PI.VolStabS.RestrProdG
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.NuInvSt
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def DetAdm : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E),
    (∀ K, IsCompact K → ν1 K < ⊤) → (∀ K, IsCompact K → ν2 K < ⊤) →
    (∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) → ν1 = ν2

def OmUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ ν1 ν2, IsOmT F E σ M J ψ (gramE σ J X0) hT ν1 →
    IsOmT F E σ M J ψ (gramE σ J X0) hT ν2 → ν1 = ν2

def OmInv : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ g : HA (AF F) σ J, IsOmT F E σ M J ψ (gramE σ J X0) hT (νX.map fun y => g • y)

theorem continuous_smul_tup {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA (AF F) σ J) :
    Continuous (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) := by

  have hm : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      Continuous fun y : Fin a → Fin M → AF F ⊗[F] E => fun i => A.mulVec (y i) := fun A =>
    continuous_pi fun i => continuous_const.matrix_mulVec (continuous_apply i)
  first
  | exact hm _
  | exact hm ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _)

theorem nuInv_of (hU : OmUniq) (hI : OmInv) : NuInv := by

  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν g s hs
  haveI : FiniteDimensional F E := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℚ F E
    | exact FiniteDimensional.right ℚ F E
  have hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) :=
    (continuous_smul_tup σ J g).measurable
  have heq := hU F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ _ _
    (hI F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν g) hν
  rw [← Measure.map_apply hm hs, heq]

theorem omUniq_of (hD : DetAdm) : OmUniq := by

  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ ν1 ν2 hν1 hν2
  haveI : FiniteDimensional F E := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℚ F E
    | exact FiniteDimensional.right ℚ F E
  refine hD F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ν1 ν2
    (fun K hK => nuFin_gen σ J _ hT ψ ν1 hν1 K hK) (fun K hK => nuFin_gen σ J _ hT ψ ν2 hν2 K hK) ?_
  rintro Φ ⟨d, b, Φinf, Φf, Φv, hc, hcs, hpure, hprod⟩
  obtain ⟨-, ⟨μinf, hμinf⟩, A1⟩ := hν1
  obtain ⟨-, -, A2⟩ := hν2
  obtain ⟨⟨νinf, hνinf⟩, B1⟩ := A1 μinf hμinf
  obtain ⟨-, B2⟩ := A2 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, C1⟩ := B1 νinf hνinf
  obtain ⟨-, C2⟩ := B2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, D1⟩ := C1 μv hμv
  obtain ⟨-, D2⟩ := C2 μv hμv
  obtain ⟨⟨fi, hfi⟩, E1⟩ := D1 νv hνv
  obtain ⟨-, E2⟩ := D2 νv hνv
  obtain ⟨⟨fv, hfv⟩, G1⟩ := E1 fi hfi
  obtain ⟨-, G2⟩ := E2 fi hfi
  obtain ⟨-, -, H1⟩ := G1 fv hfv d b Φ Φinf Φf Φv hc hcs hpure hprod
  obtain ⟨-, -, H2⟩ := G2 fv hfv d b Φ Φinf Φf Φv hc hcs hpure hprod
  rw [H1, H2]

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVDx
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

theorem gramR_add_sub {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x W : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J (x + W) - gramR R σ J x - gramR R σ J W = gramB R σ J x W := by
  funext i j
  simp only [Matrix.sub_apply, gramR, gramB, Pi.add_apply, hR_add_left, hR_add_right]
  ring

theorem gramB_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (x W W' : Fin n → Fin M → R ⊗[F] E) :
    gramB R σ J x (W + W') = gramB R σ J x W + gramB R σ J x W' := by
  funext i j
  simp only [Matrix.add_apply, gramB, Pi.add_apply, hR_add_left, hR_add_right]
  ring

theorem dxOpen_of (h : SecGram) : DxOpen := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet a _h1 _h2 v d b x hx
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)
  have : IsReduced (Fv F v ⊗[F] E) := isReduced_tens_field F E (Fv F v)
  have hss : IsSemisimpleRing (Fv F v ⊗[F] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  obtain ⟨q, hq⟩ := h F E σ hσ M J hJ hdet (Fv F v) hss a x hx
  set T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) :=
    fun S j k => ∑ i', (algebraMap F (Fv F v ⊗[F] E) (1 / 2) * S i' j) * q k i' with hT
  have hTc : Continuous T := by
    refine continuous_pi fun j => continuous_pi fun k => continuous_finsetSum _ fun i' _ => ?_
    exact (continuous_const.mul (continuous_id.matrix_elem i' j)).mul continuous_const
  have hT0 : T 0 = 0 := by
    funext j k
    simp [hT]
  set L := latSub b v a M with hL
  have hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    (PositiveNearLattice.isClopen_latV b v a M).isOpen
  set Dx : (Fin a → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ a := fun W =>
    gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x - gramH (Fv F v) σ hσ J hJ W
    with hDx
  have hDB : ∀ W, (Dx W : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) = gramB (Fv F v) σ J x W := by
    intro W
    rw [← gramR_add_sub]
    rfl
  have hDadd : ∀ W W', Dx (W + W') = Dx W + Dx W' := by
    intro W W'
    apply Subtype.ext
    rw [AddSubgroup.coe_add, hDB, hDB, hDB, gramB_add_right]
  have hDT : ∀ S : HermR (Fv F v) σ a, Dx (T S) = S := by
    intro S
    apply Subtype.ext
    rw [hDB]
    exact hq S.1 S.2
  show IsOpen (Dx '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨l, hl, rfl⟩
  have hU : IsOpen {S : HermR (Fv F v) σ a | T ((S - Dx l : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L} :=
    hLo.preimage (hTc.comp (continuous_subtype_val.comp (continuous_id.sub continuous_const)))
  refine Filter.mem_of_superset (hU.mem_nhds ?_) ?_
  · show T ((Dx l - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) ∈ L
    rw [sub_self, AddSubgroup.coe_zero, hT0]
    exact L.zero_mem
  · intro S hS
    refine ⟨l + T ((S - Dx l : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)),
      L.add_mem hl hS, ?_⟩
    rw [hDadd, hDT]
    abel

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensSt
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Filter
open scoped TensorProduct

def qV {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Nat.card (𝓞 F ⧸ v.asIdeal) : ℝ)

def QvSum : Prop := ∀ (F : Type) [Field F] [NumberField F],
  Summable fun v : HeightOneSpectrum (𝓞 F) => (qV v)⁻¹ ^ 2

def ArchPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ μinf, SdW F E σ M J (Ainf F) (psiInf F ψ) a μinf →
    ∀ νinf, SdHerm F E σ (Ainf F) (psiInf F ψ) a νinf →
    ∀ fibInf : HermR (Ainf F) σ a → Measure (Fin a → Fin M → Ainf F ⊗[F] E),
    IsFibreFamily μinf (gramR (Ainf F) σ J) Subtype.val
      {X | LinearIndependent (Ainf F ⊗[F] E) X} νinf Set.univ fibInf →
    ∃ Φinf : (Fin a → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous Φinf ∧ HasCompactSupport Φinf ∧
      ∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT)) ≠ 0

def LocPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ∃ Φv : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φv ∧
      ∫ X, Φv X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) ≠ 0

def DensAA : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ C : ℝ,
    ∀ᶠ v in cofinite,
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
    ∀ fibV : HermR (Fv F v) σ a → Measure (Fin a → Fin M → Fv F v ⊗[F] E),
    IsFibreFamily μv (gramR (Fv F v) σ J) Subtype.val
      {X | LinearIndependent (Fv F v ⊗[F] E) X} νv Set.univ fibV →
    ‖∫ X, (latV b v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) X ∂(fibV (hermOf (Fv F v) σ (gramE σ J X0) hT)) - 1‖ ≤
      C * (qV v)⁻¹ ^ 2

theorem nuNeZero_of_dens (hA : ArchPos) (hL : LocPos) (hD : DensAA) (hQ : QvSum) : NuNeZero := by
  classical
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν h0
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨⟨μinf, hμinf⟩, a1⟩ := hν.2
  obtain ⟨⟨νinf, hνinf⟩, a2⟩ := a1 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, a3⟩ := a2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, a4⟩ := a3 μv hμv
  obtain ⟨⟨fibInf, hfi⟩, a5⟩ := a4 νv hνv
  obtain ⟨⟨fibV, hfv⟩, a6⟩ := a5 fibInf hfi
  let b := Module.finBasis F E
  obtain ⟨C, hC⟩ := hD F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ _ b
  obtain ⟨Φinf, hcΦ, hcs, hIinf⟩ :=
    hA F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf fibInf hfi
  have hpos := fun v => hL F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v)
    (νv v) (hνv v) (fibV v) (hfv v)
  choose Φp hΦpSB hΦp using hpos
  let I : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    ∫ X, (latV b v).indicator (1 : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ) X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))
  have hsum : Summable fun v : HeightOneSpectrum (𝓞 F) => C * (qV v)⁻¹ ^ 2 := (hQ F).mul_left C
  have hsmall : ∀ᶠ v in cofinite, C * (qV v)⁻¹ ^ 2 < 1 :=
    hsum.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  let good : HeightOneSpectrum (𝓞 F) → Prop := fun v =>
    ‖I v - 1‖ ≤ C * (qV v)⁻¹ ^ 2 ∧ C * (qV v)⁻¹ ^ 2 < 1
  have hgood : ∀ᶠ v in cofinite, good v := by
    filter_upwards [hC, hsmall] with v hv1 hv2
    exact ⟨hv1 (μv v) (hμv v) (νv v) (hνv v) (fibV v) (hfv v), hv2⟩
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ := fun v =>
    if good v then (latV b v).indicator 1 else Φp v
  let Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ := fun Y => ∏ᶠ v, Φv v (projV v Y)
  let Φ : (Fin a → Fin M → AF F ⊗[F] E) → ℂ := fun X => Φinf (projInf X) * Φf (projFin X)
  have hSB : ∀ v, IsSB (Φv v) := fun v => by
    by_cases h : good v
    · rw [show Φv v = (latV b v).indicator 1 from if_pos h]
      exact PositiveNearLattice.isSB_latV b v a M
    · rw [show Φv v = Φp v from if_neg h]
      exact hΦpSB v
  have hpure : IsPureFin b Φf Φv := by
    refine ⟨hSB, ?_, fun _ => rfl⟩
    filter_upwards [hgood] with v hv
    exact if_pos hv
  obtain ⟨-, -, heq⟩ := a6 fibV hfv _ b Φ Φinf Φf Φv hcΦ hcs hpure (fun _ => rfl)
  rw [h0, integral_zero_measure] at heq
  let Jv : HeightOneSpectrum (𝓞 F) → ℂ := fun v =>
    ∫ X, Φv v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT))
  have hJ0 : ∀ v, Jv v ≠ 0 := fun v => by
    by_cases h : good v
    · have e : Jv v = I v := by
        simp only [Jv, I, Φv, if_pos h]
      rw [e]
      intro hI
      have := h.1
      rw [hI, zero_sub, norm_neg, norm_one] at this
      linarith [h.2]
    · have e : Jv v = ∫ X, Φp v X ∂(fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) := by
        simp only [Jv, Φv, if_neg h]
      rw [e]
      exact hΦp v
  have hJs : Summable fun v => ‖Jv v - 1‖ := by
    refine Summable.of_norm_bounded_eventually hsum ?_
    filter_upwards [hgood] with v hv
    have e : Jv v = I v := by
      simp only [Jv, I, Φv, if_pos hv]
    rw [e, norm_norm]
    exact hv.1
  have hne : ∏' v, (1 + (Jv v - 1)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (fun v => by rw [add_sub_cancel]; exact hJ0 v) hJs
  simp only [add_sub_cancel] at hne
  exact mul_ne_zero hIinf hne heq.symm

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RPGlue
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct

namespace RestrictedProductGluing

open PositiveNearLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)

def good : Set ((Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) :=
  {p | ∀ᶠ v in cofinite, p.2 v ∈ latV b v}

def mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) : Af F :=
  (⟨x, h⟩ : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])

omit [FiniteDimensional F E] in
theorem evalV_mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (mkAf x h) = x v := rfl


open Classical in
def finAd (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : Af F :=
  if h : p ∈ good b then
    mkAf (fun v => crd b (Fv F v) (p.2 v i j) k)
      ((show ∀ᶠ v in cofinite, p.2 v ∈ latV b v from h).mono fun _ hv => hv i j k)
  else 0

def crdA (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : AF F :=
  pairA F (crd b (Ainf F) (p.1 i j) k) (finAd b p i j k)

def glue (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) :
    Fin a → Fin M → AF F ⊗[F] E :=
  fun i j => (Algebra.TensorProduct.basis (AF F) b).equivFun.symm (fun k => crdA b p i j k)

theorem crd_glue (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : crd b (AF F) (glue b p i j) k = crdA b p i j k := by
  show (Algebra.TensorProduct.basis (AF F) b).repr
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm fun k => crdA b p i j k) k = _
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem measurableSet_good :
    MeasurableSet (good (F := F) (E := E) (M := M) (a := a) b) := by
  have e : good (F := F) (E := E) (M := M) (a := a) b = ⋃ S : Finset (HeightOneSpectrum (𝓞 F)),
      ⋂ v, ⋂ (_ : v ∉ S), {p | p.2 v ∈ latV b v} := by
    ext p
    simp only [good, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter, eventually_cofinite]
    constructor
    · intro h
      exact ⟨h.toFinset, fun v hv => by
        by_contra hc
        exact hv (h.mem_toFinset.2 hc)⟩
    · rintro ⟨S, hS⟩
      exact S.finite_toSet.subset fun v hv => by
        by_contra hc
        exact hv (hS v hc)
  rw [e]
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine MeasurableSet.iUnion fun S => MeasurableSet.iInter fun v =>
    MeasurableSet.iInter fun _ => ?_
  exact ((measurable_pi_apply v).comp measurable_snd)
    (isClopen_latV b v a M).isOpen.measurableSet

def coeA (x : Af F) : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v := fun v => evalV F v x

theorem measurableEmbedding_coeA : MeasurableEmbedding (coeA (F := F)) := by
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have : PolishSpace (Af F) := TopoPolish.polish_of_lcsc (Af F)
  refine Continuous.measurableEmbedding ?_ ?_
  · exact continuous_pi fun v => by exact RestrictedProduct.continuous_eval v
  · intro x y h
    exact Subtype.ext (funext fun v => congrFun h v)

theorem measurable_finAd (i : Fin a) (j : Fin M) (k : Fin d) :
    Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) := by
  classical
  have : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  refine (measurableEmbedding_coeA (F := F)).measurable_comp_iff.1 ?_
  have e : (coeA (F := F)) ∘ (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => finAd b p i j k) =
      (good b).piecewise (fun p v => crd b (Fv F v) (p.2 v i j) k) 0 := by
    funext p
    by_cases hp : p ∈ good b
    · funext v
      rw [Set.piecewise_eq_of_mem _ _ _ hp]
      simp only [Function.comp, coeA]
      rw [finAd, dite_eq_left hp, evalV_mkAf]
    · funext v
      rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      simp only [Function.comp, coeA, Pi.zero_apply]
      rw [finAd, dite_eq_right hp, map_zero]
  rw [e]
  refine Measurable.piecewise (measurableSet_good b) ?_ measurable_const
  exact Measurable.of_eval fun v => (continuous_crd b (Fv F v) k).measurable.comp
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_pi_apply v).comp measurable_snd)))

theorem measurable_crdA (i : Fin a) (j : Fin M) (k : Fin d) :
    Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) => crdA b p i j k) := by
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : BorelSpace (Af F) := ⟨rfl⟩
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hc : Continuous (fun q : Ainf F × Af F => pairA F q.1 q.2) := continuous_id
  have hx : Measurable (fun p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
      (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E) =>
      crd b (Ainf F) (p.1 i j) k) :=
    (continuous_crd b (Ainf F) k).measurable.comp
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst))
  exact hc.measurable.comp (hx.prodMk (measurable_finAd b i j k))

theorem measurable_glue :
    Measurable (glue (F := F) (E := E) (M := M) (a := a) b) := by
  have : BorelSpace (AF F) := ⟨rfl⟩
  have : BorelSpace (AF F ⊗[F] E) := ⟨rfl⟩
  have hL : Continuous (Algebra.TensorProduct.basis (AF F) b).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap
      ((Algebra.TensorProduct.basis (AF F) b).equivFun.symm.toLinearMap)
  exact Measurable.of_eval fun i => Measurable.of_eval fun j =>
    hL.measurable.comp (Measurable.of_eval fun k => measurable_crdA b i j k)

theorem glue_spec (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (hp : p ∈ good b) :
    projInf (glue b p) = p.1 ∧ ∀ v, projV v (projFin (glue b p)) = p.2 v := by
  refine ⟨?_, fun v => ?_⟩
  · funext i j
    refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
    show crd b (Ainf F) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (glue b p i j)) k =
      crd b (Ainf F) (p.1 i j) k
    rw [crd_map, crd_glue]
    rfl
  · funext i j
    refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
    show crd b (Fv F v) (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (glue b p i j))) k =
      crd b (Fv F v) (p.2 v i j) k
    rw [crd_map, crd_map, crd_glue]
    show evalV F v (finAd b p i j k) = _
    rw [finAd, dite_eq_left hp, evalV_mkAf]

end RestrictedProductGluing

theorem rpGlue_holds : RPGlue := by
  intro F E _ _ _ _ _ M a d b
  exact ⟨RestrictedProductGluing.glue b, RestrictedProductGluing.measurable_glue b,
    fun p hp => RestrictedProductGluing.glue_spec b p hp⟩

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocExOf
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem multFib_of (h2 : DensFibV) : MultFib := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μv hμv νv hνv fibV hfibV d b Φf Φv hp
  have hS := hc a ha2 (gramE σ J X0) hT hdet d b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ)) Φf Φv
    continuous_const (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero)
    Formalism.L2.SG.Pf.NcWeil.isSmoothCc_zero hp
    (fun X => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  have h3 := ((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ
  obtain ⟨μinf, hμinf⟩ := h3.1
  obtain ⟨νinf, hνinf⟩ := (h3.2 μinf hμinf).1
  obtain ⟨ginf, gv, _, hdv, hm, _⟩ := (((h3.2 μinf hμinf).2 νinf hνinf).2 μv hμv).2 νv hνv
  convert hm using 1
  funext v
  exact (h2 F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v) (νv v) (hνv v)
    (fibV v) (hfibV v) (Φv v) (gv v) (hp.1 v) (hdv v)).symm

def LatSB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (d M n : ℕ)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)),
    IsSB ((latV (M := M) (n := n) b v).indicator (1 : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ))

theorem fibPin_holds : FibPin := by
  intro F E _ _ _ _ _ σ hE M J hJ _ha _hc a _ha1 _ha2 X0 hT _hdet ψ _hψ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  have hσ : ∀ x, σ (σ x) = x := sigma_invol σ hE.2.2.2
  refine ⟨fun μinf hμinf νinf hνinf fib1 fib2 hf1 hf2 Φinf _ _ => ?_,
    fun v μv hμv νv hνv fib1 fib2 hf1 hf2 Φv _ => ?_⟩
  · have := hμinf.1
    have := hνinf.1
    rw [FibUniq.fib_eq_tens σ hσ J hJ.1 a (Ainf F) (isOpen_units_Ainf F) (lip_ainf F)
      μinf νinf fib1 fib2 hf1 hf2]
  · have := secondCountable_Fv F v
    have := locallyCompact_Fv F v
    have := hμv.1
    have := hνv.1
    rw [FibUniq.fib_eq_tens σ hσ J hJ.1 a (Fv F v) (isOpen_units_Fv F v) (TensAllW.lip_field _)
      μv νv fib1 fib2 hf1 hf2]

theorem fibPin_of (_h1 : DensFibInf) (_h2 : DensFibV) (_hL : LatSB) : FibPin := fibPin_holds

theorem locEx_of (hI : FibInfEx) (hV : FibVEx) (hL : LatSB) : LocEx := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hE.2.2.1]; norm_num)
  let b := Module.finBasis F E
  let Lv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => (latV b v).indicator 1
  have hp : IsPureFin b (fun X => ∏ᶠ v, Lv v (projV v X)) Lv :=
    ⟨fun v => hL F E _ M a b v, Filter.Eventually.of_forall fun v => rfl, fun X => rfl⟩
  have hS := hc a ha2 (gramE σ J X0) hT hdet _ b (fun _ => (0 : ℂ)) (fun _ => (0 : ℂ))
    (fun X => ∏ᶠ v, Lv v (projV v X)) Lv continuous_const
    (rapidDecay_of_compact b _ continuous_const HasCompactSupport.zero)
    Formalism.L2.SG.Pf.NcWeil.isSmoothCc_zero hp (fun X => by simp)
  obtain ⟨μ, hμ⟩ := hS.1
  obtain ⟨𝓕, h𝓕⟩ := (hS.2 μ hμ).1
  have h3 := ((hS.2 μ hμ).2 𝓕 h𝓕).2 ψ hψ
  obtain ⟨μinf, hμinf⟩ := h3.1
  obtain ⟨νinf, hνinf⟩ := (h3.2 μinf hμinf).1
  have h4 := ((h3.2 μinf hμinf).2 νinf hνinf)
  obtain ⟨μv, hμv⟩ := h4.1
  obtain ⟨νv, hνv⟩ := (h4.2 μv hμv).1
  obtain ⟨fibInf, hfi⟩ := hI F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμinf νinf hνinf
  choose fibV hfv using fun v =>
    hV F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v (μv v) (hμv v) (νv v) (hνv v)
  exact ⟨μinf, νinf, μv, νv, fibInf, fibV, hμinf, hνinf, hμv, hνv, hfi, hfv⟩

theorem exOmT_of_steps (hI : FibInfEx) (hV : FibVEx) (hL : LatSB) (hU : SdUniq)
    (hDI : DensFibInf) (hDV : DensFibV) (hR : RestrProd) : ExOmT :=
  exOmT_of (locEx_of hI hV hL) hU (fibPin_of hDI hDV hL) (multFib_of hDV) hR

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FiniteOnCompacts
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct

namespace RestrictedProductFiber

theorem finite_on_compacts {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] [LocallyCompactSpace V] [T2Space V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (U : Set V) (hU : IsOpen U)
    (ν : Measure X) (B : Set X) (fib : X → Measure V) (h : IsFibreFamily μ f ι U ν B fib)
    (b : X) (hb : b ∈ B) (hC : IsClosed (f ⁻¹' {ι b})) (hCU : f ⁻¹' {ι b} ⊆ U) :
    IsFiniteMeasureOnCompacts (fib b) := by
  refine ⟨fun K hK => ?_⟩
  have hK' : IsCompact (K ∩ f ⁻¹' {ι b}) := hK.inter_right hC
  obtain ⟨φ, h1, hφc, hφU, _h01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK' hU (Set.inter_subset_right.trans hCU)
  have hint : Integrable φ (fib b) :=
    (h.2.2 φ φ.continuous hφc hφU).1 b hb
  have hnull : fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0 := h.1 b
  have hM : fib b (K ∩ f ⁻¹' {ι b}) ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib b) := by
    have hm : AEMeasurable (fun x => ENNReal.ofReal (φ x)) (fib b) :=
      (ENNReal.continuous_ofReal.comp φ.continuous).measurable.aemeasurable
    calc fib b (K ∩ f ⁻¹' {ι b}) ≤ fib b {x | 1 ≤ ENNReal.ofReal (φ x)} := by
          refine measure_mono fun x hx => ?_
          simp only [Set.mem_ofPred_eq, h1 hx, Pi.one_apply, ENNReal.ofReal_one, le_refl]
      _ = 1 * fib b {x | 1 ≤ ENNReal.ofReal (φ x)} := (one_mul _).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib b) := mul_meas_ge_le_lintegral₀ hm 1
  calc fib b K ≤ fib b ((K ∩ f ⁻¹' {ι b}) ∪ (f ⁻¹' {ι b} ∩ U)ᶜ) := by
        refine measure_mono fun x hx => ?_
        by_cases hx2 : x ∈ f ⁻¹' {ι b} ∩ U
        · exact Or.inl ⟨hx, hx2.1⟩
        · exact Or.inr hx2
    _ ≤ fib b (K ∩ f ⁻¹' {ι b}) + fib b (f ⁻¹' {ι b} ∩ U)ᶜ := measure_union_le _ _
    _ = fib b (K ∩ f ⁻¹' {ι b}) := by rw [hnull, add_zero]
    _ < ⊤ := lt_of_le_of_lt hM hint.lintegral_lt_top

theorem fib_props {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (hTF : TensFacts F E σ M J a R)
    (T : Matrix (Fin a) (Fin a) E) (hT : ∀ i j, σ (T j i) = T i j) (hdet : T.det ≠ 0)
    (μ : Measure (Fin a → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ a))
    (fib : HermR R σ a → Measure (Fin a → Fin M → R ⊗[F] E))
    (h : IsFibreFamily μ (gramR R σ J) Subtype.val
      {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ fib) :
    SigmaFinite (fib (hermOf R σ T hT)) ∧
    ∀ Φ : (Fin a → Fin M → R ⊗[F] E) → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable Φ (fib (hermOf R σ T hT)) := by
  obtain ⟨h1, h2, h3, _h4, h5, _h6, h7⟩ := hTF
  have : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have : T2Space (Matrix (Fin a) (Fin a) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → R ⊗[F] E))
  have hC : IsClosed (gramR R σ J ⁻¹' {((hermOf R σ T hT : HermR R σ a) :
      Matrix (Fin a) (Fin a) (R ⊗[F] E))}) := isClosed_singleton.preimage h5
  have hCU : gramR R σ J ⁻¹' {((hermOf R σ T hT : HermR R σ a) :
      Matrix (Fin a) (Fin a) (R ⊗[F] E))} ⊆ {X | LinearIndependent (R ⊗[F] E) X} := by
    intro X hX
    have hX' : gramR R σ J X = ((hermOf R σ T hT : HermR R σ a) :
        Matrix (Fin a) (Fin a) (R ⊗[F] E)) := hX
    have hu := isUnit_det_hermOf R σ T hT hdet
    rw [← hX'] at hu
    exact linIndep_of_isUnit_det R σ J X hu
  have hfin := finite_on_compacts μ (gramR R σ J) Subtype.val _ h7 ν Set.univ fib h
    (hermOf R σ T hT) (Set.mem_univ _) hC hCU
  have : SigmaCompactSpace (Fin a → Fin M → R ⊗[F] E) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  exact ⟨inferInstance, fun Φ hc hs => hc.integrable_of_hasCompactSupport hs⟩

end RestrictedProductFiber

theorem rpFib_holds : RPFib := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hI, hV⟩ := tensAll_holds F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨fun μ ν fib h => RestrictedProductFiber.fib_props σ J a (Ainf F) hI _ hT hdet μ ν fib h,
    fun v μ ν fib h => RestrictedProductFiber.fib_props σ J a (Fv F v) (hV v) _ hT hdet μ ν fib h⟩

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdA
noncomputable section

namespace PI.VolStabS.RestrProdA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem hasProd_compl_of_ne_zero {β : Type} {f : β → ℂ} {p : ℂ} (h : HasProd f p) (S : Finset β)
    (hS : ∀ b ∈ S, f b ≠ 0) :
    HasProd ({b | b ∉ S}.mulIndicator f) (p * ∏ b ∈ S, (f b)⁻¹) := by
  classical
  have h2 : HasProd (fun b => if b ∈ S then (f b)⁻¹ else 1)
      (∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1)) := hasProd_prod_of_ne_finset_one fun b hb => if_neg hb
  have e : ∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1) = ∏ b ∈ S, (f b)⁻¹ :=
    Finset.prod_congr rfl fun b hb => if_pos hb
  rw [e] at h2
  convert h.mul h2 using 1
  funext b
  by_cases hb : b ∈ S
  · simp [Set.mulIndicator, hb, hS b hb]
  · simp [Set.mulIndicator, hb]

theorem hasProd_ofReal_of_complex {β : Type} {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) {q : ℂ}
    (h : HasProd (fun b => (f b : ℂ)) q) :
    HasProd (fun b => ENNReal.ofReal (f b)) (ENNReal.ofReal q.re) := by
  unfold HasProd at h ⊢
  have h1 := ((ENNReal.continuous_ofReal.comp Complex.continuous_re).tendsto q).comp h
  refine h1.congr fun s => ?_
  simp only [Function.comp_apply, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact ENNReal.ofReal_prod_of_nonneg fun b _ => hf b

theorem rpTail_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
    (hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ → Integrable Φ (m v))
    (hmult : ∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv → Multipliable (fun v => ∫ X, Φv v X ∂(m v))) :
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} => m v.1 (latV b v.1)) c := by
  classical
  by_cases h0 : ∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0
  · exact Or.inl h0
  refine Or.inr fun S => ?_
  push_neg at h0
  choose g hgSB hg0 using h0
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => if v ∈ S then g v else (latV b v).indicator 1
  have hpure : IsPureFin b (fun Y => ∏ᶠ v, Φv v (projV v Y)) Φv := by
    refine ⟨fun v => ?_, ?_, fun Y => rfl⟩
    · by_cases hv : v ∈ S
      · simp only [Φv, hv, if_true]; exact hgSB v
      · simp only [Φv, hv, if_false]; exact PositiveNearLattice.isSB_latV b v a M
    · refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
      by_contra h
      exact hv (if_neg h)
  have hP := (hmult _ Φv hpure).hasProd
  have hne : ∀ v ∈ S, ∫ X, Φv v X ∂(m v) ≠ 0 := fun v hv => by
    simp only [Φv, hv, if_true]; exact hg0 v
  have h1 := hasProd_compl_of_ne_zero hP S hne
  have hL : ∀ v, MeasurableSet (latV (M := M) (n := a) b v) := fun v =>
    (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet
  have hfin : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
    have h := hSB v _ (PositiveNearLattice.isSB_latV b v a M)
    rw [integrable_indicator_iff (hL v)] at h
    exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
  have e : {v | v ∉ S}.mulIndicator (fun v => ∫ X, Φv v X ∂(m v)) =
      fun v => (({v | v ∉ S}.mulIndicator (fun v => (m v (latV b v)).toReal) v : ℝ) : ℂ) := by
    funext v
    by_cases hv : v ∈ S
    · simp [Set.mulIndicator, hv]
    · simp only [Set.mulIndicator, Set.mem_setOf_eq, hv, not_false_eq_true, if_true, Φv, if_false]
      rw [integral_indicator (hL v)]
      simp [Measure.real]
  rw [e] at h1
  have h2 := hasProd_ofReal_of_complex (fun v => by
    by_cases hv : v ∈ S <;> simp [Set.mulIndicator, hv]) h1
  have e2 : (fun v => ENNReal.ofReal ({v | v ∉ S}.mulIndicator
      (fun v => (m v (latV b v)).toReal) v)) = {v | v ∉ S}.mulIndicator (fun v => m v (latV b v)) := by
    funext v
    by_cases hv : v ∈ S
    · simp [Set.mulIndicator, hv]
    · simp [Set.mulIndicator, hv, ENNReal.ofReal_toReal (hfin v)]
  rw [e2] at h2
  exact ⟨_, ENNReal.ofReal_ne_top, (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ S})).2 h2⟩

theorem repr_change {F E : Type} [Field F] [Field E] [Algebra F E] {d d' : ℕ}
    (R : Type) [CommRing R] [Algebra F R] (b : Module.Basis (Fin d) F E)
    (b' : Module.Basis (Fin d') F E) (y : R ⊗[F] E) (k' : Fin d') :
    (Algebra.TensorProduct.basis R b').repr y k' =
      ∑ k, (Algebra.TensorProduct.basis R b).repr y k * algebraMap F R (b'.repr (b k) k') := by
  have hE : ∀ e : E, b'.repr e k' = ∑ k, b.repr e k * b'.repr (b k) k' := fun e => by
    conv_lhs => rw [← b.sum_repr e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, hE,
      map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_mul, mul_assoc]
  | add x y hx hy =>
    rw [map_add (f := _), Finsupp.add_apply, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add (f := _), Finsupp.add_apply, add_mul]

theorem latCofin_holds : LatCofin := by
  intro F E _ _ _ _ a M d d' b b'
  have key : ∀ x : F, ∀ᶠ v in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ (v.adicCompletionIntegers F : Set (Fv F v)) := fun x =>
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ k k', algebraMap F (Fv F v) (b'.repr (b k) k') ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun k' => key _
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ k' k, algebraMap F (Fv F v) (b.repr (b' k') k) ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Filter.eventually_all.2 fun k' => Filter.eventually_all.2 fun k => key _
  filter_upwards [h1, h2] with v hv1 hv2
  ext Y
  simp only [latV, Set.mem_setOf_eq]
  constructor
  · intro hY x i k'
    rw [repr_change (Fv F v) b b']
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hY x i k) (hv1 k k')
  · intro hY x i k
    rw [repr_change (Fv F v) b' b]
    exact Subring.sum_mem _ fun k' _ => Subring.mul_mem _ (hY x i k') (hv2 k' k)

theorem rpTail_holds : RPTail := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV d b hSB hmult
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact rpTail_gen b (fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) hSB hmult

end PI.VolStabS.RestrProdA
end
end
