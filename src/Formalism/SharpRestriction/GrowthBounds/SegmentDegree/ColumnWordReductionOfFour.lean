module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Coarse

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SegmentReductionOfColumnWords
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNeZeroOfResidueNeZero
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def zSeg (O : Type) [CommRing O] (j : ℤ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) : SegRing O r K :=
  plEmb O r K (X.DlSeg p K O j) * expand (p ^ X.Rj p K j) y * monomial e 1

def IsEll (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : Prop :=
  (∀ v, e v ≠ 0 → v.1 ∈ X.toLate j) ∧ ∀ v, e v < p ^ X.Rj p K j

def Step2 (j : ℤ) (b : ℤ → ℕ) : Prop :=
  ∀ z ∈ X.F.LLset j,
    (X.a' p K (posOf n' z) : ℝ) / (p : ℝ) ^ (X.F.dist j z + X.Rj p K j) - k (r := r) K < (b z : ℝ)

end Dat

def CoarseLabelFactorisation : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O],
    X.Hyp p K → ∀ l, X.IsCLabel p K l →
    ∃ (l0 : Fin n' × Fin (r + K) →₀ ℕ) (e : ℤ → (ℤ × Fin (r + K) →₀ ℕ)), IsLabel p X.F l0 ∧
      (∀ j, X.IsEll p K j (e j)) ∧
      (monomial l 1 : RRing O n' (r + K)) =
        monomial l0 1 * ∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (monomial (e j) 1)

def TopDegreeComparison : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O],
    X.Hyp p K → ∀ (b : ℤ → ℤ → ℕ) (y : ℤ → SegRing O r K) (l : Fin n' × Fin (r + K) →₀ ℕ),
      (∀ j, y j ∈ X.Mj p K O j (b j)) → X.IsCLabel p K l →
      (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ∈ RRdeg O n' (r + K) (X.a' p K) →
      (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ≠ 0 →
      ∀ j ∈ Finset.range X.F.J, X.Step2 p K (j : ℤ) (b j)

def DiscriminantMultihomogeneous : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O],
    X.Dl p K O ∈ RRdeg O n' (r + K) (X.Et p K)

def DiscriminantNeZero : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], X.Hyp p K → X.Dl p K O ≠ 0

theorem discriminant_ne_zero_of_residue_ne_zero (h : DiscriminantNonzeroModUniformiser) : DiscriminantNeZero := by
  intro p n' r K _ _ _ X O _ _ _ hX h0
  exact h p n' r K X O hX (by rw [h0, map_zero])

def TopCountLowerBounds (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    (∀ t ∈ X.F.TT, (9 / 10 : ℝ) * (X.deg t : ℝ) ≤ (X.a' p K t : ℝ)) ∧ ∀ t, X.Et p K t ≤ X.d t

def SegmentReductionLiftsMultihomogeneous (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ),
      y ∈ X.Mj p K O j b → X.IsEll p K j e → X.Step2 p K j b →
      ∀ β : ℤ → ℕ, X.zSeg p K O j y e ∈ Pol O (r + K) β →
      ∃ x ∈ X.XXs p K O j, x ∈ Pol O (r + K) β ∧
        MvPolynomial.map (IsLocalRing.residue O) x = MvPolynomial.map (IsLocalRing.residue O) (X.zSeg p K O j y e)

def SegmentImageMultihomogeneous : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O]
    (j : ℤ) (b : ℤ → ℕ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ),
    y ∈ Pol O (r + K) b → ∃ β : ℤ → ℕ, X.zSeg p K O j y e ∈ Pol O (r + K) β

def SegmentProductDegreeDetermined : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] (F : Frames n' r) (O : Type) [CommRing O]
    (x z : ℤ → SegRing O r K) (β : ℤ → ℤ → ℕ) (l0 : Fin n' × Fin (r + K) →₀ ℕ) (d : Fin n' → ℕ),
    (∀ j, x j ∈ Pol O (r + K) (β j)) → (∀ j, z j ∈ Pol O (r + K) (β j)) →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1 ∈ RRdeg O n' (r + K) d →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1 ≠ 0 →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l0 1 ∈ RRdeg O n' (r + K) d

theorem RRdeg_eq_Pol (O : Type) [CommRing O] (n' k : ℕ) (d : Fin n' → ℕ) : RRdeg O n' k d = Pol O k d := rfl

theorem segDeg_eq_Pol (O : Type) [CommRing O] (r K : ℕ) (b : ℤ → ℕ) :
    restrictSupport O (Dat.segDegSet (r := r) K b) = Pol O (r + K) b := rfl

theorem map_phSeg {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (K p : ℕ) {n' r : ℕ} [NeZero n']
    (F : Frames n' r) (j : ℤ) (P : SegRing R r K) :
    MvPolynomial.map f (phSeg R K p F j P) = phSeg S K p F j (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [phSeg]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | mul_X q v h =>
    simp only [map_mul, h, map_X]
    simp [phSeg]

theorem phc_eq {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ) (y : SegRing O r K) :
    X.phc p K O j y = phSeg O K p X.F j (expand (p ^ X.Rj p K j) y) := by
  have : X.phc p K O j = (phSeg O K p X.F j).comp (expand (p ^ X.Rj p K j)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Dat.phc, phSeg, AlgHom.comp_apply, expand_X, aeval_X, map_pow]
    rw [← pow_mul, ← pow_add]
  rw [this]; rfl

theorem generator_of_segment_reductions (C₀ : ℝ) (hLab : CoarseLabelFactorisation) (hDeg2 : TopDegreeComparison) (hDlHom : DiscriminantMultihomogeneous) (hDlNe : DiscriminantNeZero)
    (h41b : TopCountLowerBounds C₀) (hSeg : SegmentReductionLiftsMultihomogeneous C₀) (hZ : SegmentImageMultihomogeneous) (hHom : SegmentProductDegreeDetermined) : GeneratorModuloUniformiser C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk u hu
  obtain ⟨b, y, l, hy, hl, hueq, hdeg⟩ := hu
  have hJ : 1 ≤ X.F.J := hX.valid.1
  have hp0 : 0 < p := hX.prime.pos
  by_cases hu0 : u = 0
  · refine ⟨0, ⟨fun _ => 0, fun _ => Submodule.zero_mem _, 0, ?_, ?_, Submodule.zero_mem _⟩, by simp [hu0]⟩
    · intro j x _ _ c
      simpa using Nat.pow_pos hp0
    · have h0 : (∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) ((fun _ : ℤ => (0 : SegRing O r K)) (j : ℤ))) = 0 :=
        Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hJ) (map_zero _)
      rw [h0, zero_mul]
  obtain ⟨l0, e, hl0, he, hmon⟩ := hLab p n' r K X O hX l hl
  set z : ℤ → SegRing O r K := fun j => X.zSeg p K O j (y j) (e j) with hz
  have hDu : X.Dl p K O * u = (∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (z j)) * monomial l0 1 := by
    rw [hueq, hmon]
    simp only [hz, Dat.zSeg, Dat.Dl, map_mul, Finset.prod_mul_distrib, phc_eq]
    ring
  have hβ : ∀ j, ∃ β : ℤ → ℕ, z j ∈ Pol O (r + K) β := fun j =>
    hZ p n' r K X O j (b j) (y j) (e j) (by rw [← segDeg_eq_Pol]; exact (hy j).1.2)
  choose β hβ using hβ
  have h2 := hDeg2 p n' r K X O hX b y l hy hl (hueq ▸ hdeg) (hueq ▸ hu0)
  have hx : ∀ j : ℤ, ∃ x, x ∈ X.XXs p K O j ∧ x ∈ Pol O (r + K) (β j) ∧
      ((∃ i ∈ Finset.range X.F.J, (i : ℤ) = j) →
        MvPolynomial.map (IsLocalRing.residue O) x = MvPolynomial.map (IsLocalRing.residue O) (z j)) := by
    intro j
    by_cases hj : ∃ i ∈ Finset.range X.F.J, (i : ℤ) = j
    · obtain ⟨i, hi, rfl⟩ := hj
      obtain ⟨x, h1, h2', h3⟩ := hSeg p n' r K X O S hX hLa hk (i : ℤ) (b i) (y i) (e i) (hy i) (he i) (h2 i hi)
        (β i) (hβ i)
      exact ⟨x, h1, h2', fun _ => h3⟩
    · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, fun h => absurd h hj⟩
  choose x hx1 hx2 hx3 using hx
  have hsum : X.Et p K + X.a' p K = X.d := by
    funext t
    have := (h41b p n' r K X hX hLa hk).2 t
    simp only [Pi.add_apply, Dat.a']
    omega
  have hDdeg : X.Dl p K O * u ∈ RRdeg O n' (r + K) X.d := by
    have h1 : X.Dl p K O ∈ Pol O (r + K) (X.Et p K) := by
      rw [← RRdeg_eq_Pol]; exact hDlHom p n' r K X O
    have h2 : u ∈ Pol O (r + K) (X.a' p K) := by
      rw [← RRdeg_eq_Pol]; exact hdeg
    have := hom_Pol_mul O h1 h2
    rw [hsum] at this
    rw [RRdeg_eq_Pol]
    exact this
  have hDne : X.Dl p K O * u ≠ 0 := mul_ne_zero (hDlNe p n' r K X O hX) hu0
  refine ⟨(∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (x j)) * monomial l0 1,
    ⟨x, hx1, l0, hl0, rfl, ?_⟩, ?_⟩
  · exact hHom p n' r K X.F O x z β l0 X.d hx2 hβ (hDu ▸ hDdeg) (hDu ▸ hDne)
  · rw [hDu]
    simp only [map_mul, map_prod, map_phSeg]
    rw [Finset.prod_congr rfl fun i hi => by rw [← hx3 (i : ℤ) ⟨i, hi, rfl⟩]]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def ColumnWordReductionLifts (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ) (e : ℤ × Fin (r + K) →₀ ℕ), X.IsEll p K j e → X.Step2 p K j b →
    ∀ q ∈ segPairs X.F j K (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j),
    ∀ I' I'', IsSt q.1 I' → IsSt q.2 I'' →
      ∃ x ∈ X.XXs p K O j, MvPolynomial.map (IsLocalRing.residue O) x =
        MvPolynomial.map (IsLocalRing.residue O)
          (X.zSeg p K O j (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) e)

theorem map_suppProj {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (s : Set (σ →₀ ℕ))
    (A : MvPolynomial σ R) : MvPolynomial.map f (suppProj R s A) = suppProj S s (MvPolynomial.map f A) := by
  classical
  ext m
  rw [coeff_map, coeff_suppProj, coeff_suppProj, coeff_map]
  split_ifs <;> simp

theorem plEmb_Pol {R : Type} [CommRing R] (r K : ℕ) {d : ℤ → ℕ} {A : MvPolynomial (ℤ × Fin r) R}
    (hA : A ∈ Pol R r d) : plEmb R r K A ∈ Pol R (r + K) d := by
  classical
  have hf : Function.Injective (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)
  rw [mem_Pol_iff] at hA ⊢
  intro m hm i
  unfold plEmb at hm
  rw [support_rename_of_injective hf] at hm
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  rw [← hA u hu i]
  unfold multideg
  rw [Fin.sum_univ_add]
  have z1 : ∀ c : Fin r, Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) u (i, Fin.castAdd K c)
      = u (i, c) := fun c => Finsupp.mapDomain_apply_of_injective hf u (i, c)
  have z2 : ∀ c : Fin K, Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) u (i, Fin.natAdd r c)
      = 0 := by
    intro c
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨v, hv⟩
    simp only [Prod.mk.injEq] at hv
    have := congrArg Fin.val hv.2
    simp at this
    omega
  simp only [z1, z2, Finset.sum_const_zero, add_zero]

theorem nmEmb_Pol {R : Type} [CommRing R] (r K : ℕ) {d : ℤ → ℕ} {A : MvPolynomial (ℤ × Fin K) R}
    (hA : A ∈ Pol R K d) : nmEmb R r K A ∈ Pol R (r + K) d := by
  classical
  have hf : Function.Injective (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) := by
    intro x y h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.natAdd_injective _ _ h.2)
  rw [mem_Pol_iff] at hA ⊢
  intro m hm i
  unfold nmEmb at hm
  rw [support_rename_of_injective hf] at hm
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
  rw [← hA u hu i]
  unfold multideg
  rw [Fin.sum_univ_add]
  have z1 : ∀ c : Fin K, Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) u (i, Fin.natAdd r c)
      = u (i, c) := fun c => Finsupp.mapDomain_apply_of_injective hf u (i, c)
  have z2 : ∀ c : Fin r, Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) u (i, Fin.castAdd K c)
      = 0 := by
    intro c
    refine Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨v, hv⟩
    simp only [Prod.mk.injEq] at hv
    have := congrArg Fin.val hv.2
    simp at this
    omega
  simp only [z1, z2, Finset.sum_const_zero, zero_add]

theorem geR_mono {v v' : WithTop ℤ} {t : ℝ} (h : geR v t) (hv : v ≤ v') : geR v' t := by
  intro z hz
  rw [hz] at hv
  induction v using WithTop.recTopCoe with
  | top => simp at hv
  | coe z0 =>
    have h1 : z0 ≤ z := WithTop.coe_le_coe.mp hv
    exact (h z0 rfl).trans (by exact_mod_cast h1)

theorem XX'_polComp (O : Type) [CommRing O] (r K : ℕ) [NeZero r] [NeZero K] {n' : ℕ} [NeZero n'] (F : Frames n' r)
    (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ) (β : ℤ → ℕ) {x : SegRing O r K} (hx : x ∈ XX' O r K F j m th o) :
    polComp O (r + K) β x ∈ XX' O r K F j m th o := by
  classical
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  have hx2' := hx2
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · clear hx hx2 hx2'
    induction hx1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨A, G, M, hA, hG, hc, rfl⟩ := hy
      obtain ⟨T', hT'⟩ := exists_sum_polComp O r A
      obtain ⟨T'', hT''⟩ := exists_sum_polComp O K G
      have hsum : plEmb O r K A * nmEmb O r K G = ∑ d' ∈ T', ∑ d'' ∈ T'',
          plEmb O r K (polComp O r d' A) * nmEmb O r K (polComp O K d'' G) := by
        conv_lhs => rw [hT', hT'']
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.sum_mul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsum, map_sum]
      refine Submodule.sum_mem _ fun d' _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Submodule.sum_mem _ fun d'' _ => ?_
      have hP : plEmb O r K (polComp O r d' A) * nmEmb O r K (polComp O K d'' G) ∈ Pol O (r + K) (d' + d'') :=
        hom_Pol_mul O (plEmb_Pol r K (polComp_mem_Pol O r d' A)) (nmEmb_Pol r K (polComp_mem_Pol O K d'' G))
      by_cases hd : β = d' + d''
      · rw [hd, polComp_of_mem O _ _ _ hP]
        refine Submodule.subset_span ⟨_, _, M, polComp_mem_supported O r d' A _ hA,
          polComp_mem_supported O K d'' G _ hG, fun x hx hW => ?_, rfl⟩
        obtain ⟨cE, cO, cR⟩ := hc x hx hW
        exact ⟨fun he => ⟨(lowest_degree_compose_le _ _ d'' G).trans (cE he).1, (cE he).2.trans (valS_le_polComp _ _ d' A)⟩,
          fun he => ⟨(lowest_degree_compose_le _ _ d'' G).trans (cO he).1, (cO he).2.trans (valS_le_polComp _ _ d' A)⟩,
          geR_mono cR (valS_le_polComp _ _ d' A)⟩
      · rw [polComp_of_ne O _ _ _ _ hP hd]
        exact Submodule.zero_mem _
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  · rw [mem_restrictSupport_iff] at hx2 ⊢
    intro mm hmm
    exact hx2 (Finset.mem_coe.mpr (suppProj_support_subset O _ x (Finset.mem_coe.mp hmm)))

theorem zSeg_add {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ)
    (y1 y2 : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) :
    X.zSeg p K O j (y1 + y2) e = X.zSeg p K O j y1 e + X.zSeg p K O j y2 e := by
  unfold Dat.zSeg; rw [map_add (f := _)]; ring

theorem zSeg_smul {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ) (c : O)
    (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) :
    X.zSeg p K O j (c • y) e = c • X.zSeg p K O j y e := by
  unfold Dat.zSeg; rw [map_smul, mul_smul_comm, smul_mul_assoc]

theorem segment_reduction_of_column_words (D : Formalism.BasicNotions.D7) (hB12 : NestedTypeBound D) (C₀ : ℝ) (hW : ColumnWordReductionLifts C₀) : SegmentReductionLiftsMultihomogeneous C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b y e hy he h2 β hβ
  have : Fact p.Prime := ⟨hX.prime⟩
  have hseg : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h1 := (hB12 p O S n' r K X.F X.L₁ X.N₁ j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) hX.valid hseg
    (fun _ => Int.natCast_nonneg _)).1
  have hy1 : y ∈ XX' O r K X.F j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) := hy.1.1
  rw [h1] at hy1
  unfold Formalism.MainNotions.CovariantDegrees.XXZ at hy1
  rw [Submodule.map_span] at hy1
  have key : ∃ x ∈ X.XXs p K O j, MvPolynomial.map (IsLocalRing.residue O) x =
      MvPolynomial.map (IsLocalRing.residue O) (X.zSeg p K O j y e) := by
    clear hβ hy
    induction hy1 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨_, ⟨q, hq, I', I'', hI', hI'', rfl⟩, rfl⟩ := hy
      exact hW p n' r K X O S hX hLa hk j b e he h2 q hq I' I'' hI' hI''
    | zero => exact ⟨0, Submodule.zero_mem _, by simp [Dat.zSeg]⟩
    | add y z _ _ hy hz =>
      obtain ⟨x1, hx1, e1⟩ := hy
      obtain ⟨x2, hx2, e2⟩ := hz
      exact ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, by rw [zSeg_add, map_add (f := _), map_add (f := _), e1, e2]⟩
    | smul c y _ hy =>
      obtain ⟨x1, hx1, e1⟩ := hy
      refine ⟨c • x1, Submodule.smul_mem _ c hx1, ?_⟩
      rw [zSeg_smul, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_mul, e1]
  obtain ⟨x, hx, hxe⟩ := key
  refine ⟨polComp O (r + K) β x, XX'_polComp O r K X.F j _ _ _ β hx, polComp_mem_Pol O _ β x, ?_⟩
  unfold polComp
  rw [map_suppProj, hxe, ← map_suppProj]
  congr 1
  exact polComp_of_mem O _ β _ hβ

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def ellP (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : MvPolynomial (ℤ × Fin r) R :=
  ∏ x ∈ X.toLate j, ∏ c : Fin r, MvPolynomial.X (x, c) ^ e (x, Fin.castAdd K c)

def ellN (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : MvPolynomial (ℤ × Fin K) R :=
  ∏ x ∈ X.toLate j, ∏ c : Fin K, MvPolynomial.X (x, c) ^ e (x, Fin.natAdd r c)

def dS (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : ℕ :=
  ∑ x ∈ X.toLate j, if Even x then 0 else ∑ c : Fin r, e (x, Fin.castAdd K c)

def dV (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : ℕ :=
  ∑ x ∈ X.toLate j, if Even x then ∑ c : Fin K, e (x, Fin.natAdd r c) else 0

def Aw (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (nu : Fin (segN X.F j + 1) → Fin r → ℤ)
    (I' : ℤ → Finset (Fin r)) : MvPolynomial (ℤ × Fin r) R :=
  (segRen X.F j R r (Psi R nu I')) ^ (p ^ X.Rj p K j) * X.ellP K R j e * X.DlSeg p K R j

def Gw (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (ka : Fin (segN X.F j + 1) → Fin K → ℤ)
    (I'' : ℤ → Finset (Fin K)) : MvPolynomial (ℤ × Fin K) R :=
  (segRen X.F j R K (Psi R ka I'')) ^ (p ^ X.Rj p K j) * X.ellN K R j e

def Mw [NeZero K] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (ka : Fin (segN X.F j + 1) → Fin K → ℤ) : ℤ → ℤ :=
  Function.extend (segE X.F j)
    (fun i => ((p ^ X.Rj p K j : ℕ) : ℤ) * (if Even (segE X.F j i) then ka i.succ 0 else ka i.castSucc 0) +
      (X.dV K j e : ℤ)) 0

end Dat

structure WCtx (C₀ : ℝ) (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r)
    (j : ℤ) (b : ℤ → ℕ) (e : ℤ × Fin (r + K) →₀ ℕ)
    (q : (Fin (segN X.F j + 1) → Fin r → ℤ) × (Fin (segN X.F j + 1) → Fin K → ℤ))
    (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)) : Prop where
  hX : X.Hyp p K
  hLa : C₀ ≤ X.CLa
  hk : C₀ ≤ X.Ck
  he : X.IsEll p K j e
  h2 : X.Step2 p K j b
  hq : q ∈ segPairs X.F j K (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j)
  hI' : IsSt q.1 I'
  hI'' : IsSt q.2 I''

def FrobeniusReductionProduct (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    MvPolynomial.map (IsLocalRing.residue O)
        (X.zSeg p K O j (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) e) =
      plEmb (FF O) r K (X.Aw p K (FF O) j e q.1 I') * nmEmb (FF O) r K (X.Gw p K (FF O) j e q.2 I'')

def ProductAllowedLetters (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    X.Aw p K (FF O) j e q.1 I' ∈ supported (FF O) {v : ℤ × Fin r | v.1 ∈ X.F.letters j} ∧
    X.Gw p K (FF O) j e q.2 I'' ∈ supported (FF O) {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1}

def ColumnConditionsWithMargin (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} (X.Gw p K (FF O) j e q.2 I'') ≤ ((X.Mw p K j e q.2 x : ℤ) : WithBot ℤ) ∧
          ((X.Mw p K j e q.2 x + X.mg p K j x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} (X.Aw p K (FF O) j e q.1 I')) ∧
      (¬ Even x → lam1S LZ {y | y < x} (X.Gw p K (FF O) j e q.2 I'') ≤ ((X.Mw p K j e q.2 x : ℤ) : WithBot ℤ) ∧
          ((X.Mw p K j e q.2 x + X.mg p K j x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} (X.Aw p K (FF O) j e q.1 I')) ∧
      geR (valS LZ {y | y < x} (X.Aw p K (FF O) j e q.1 I')) (X.th p j x)

def ProductOrdersBounded (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    ∀ mm ∈ (plEmb (FF O) r K (X.Aw p K (FF O) j e q.1 I') * nmEmb (FF O) r K (X.Gw p K (FF O) j e q.2 I'')).support,
      ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → (ordDeg mm x : ℝ) ≤ X.o p K j x

theorem column_word_reduction_of_four (D : Formalism.BasicNotions.D7) (hB12 : NestedTypeBound D) (C₀ : ℝ) (h1 : FrobeniusReductionProduct C₀) (h2 : ProductAllowedLetters C₀)
    (h3 : ColumnConditionsWithMargin C₀) (h4 : ProductOrdersBounded C₀) : ColumnWordReductionLifts C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b e he hs2 q hq I' I'' hI' hI''
  have : Fact p.Prime := ⟨hX.prime⟩
  have hc : WCtx C₀ p n' r K X j b e q I' I'' := ⟨hX, hLa, hk, he, hs2, hq, hI', hI''⟩
  have hseg : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h6 := (hB12 p O S n' r K X.F X.L₁ X.N₁ j (X.mg p K j) (X.th p j) (X.o p K j) hX.valid hseg
    (fun x => by unfold Dat.mg; positivity)).2.2.2.2.2
  obtain ⟨P, hP, hPe⟩ := h6 (X.Aw p K (FF O) j e q.1 I') (X.Gw p K (FF O) j e q.2 I'') (X.Mw p K j e q.2)
    (h2 p n' r K X O S j b e q I' I'' hc).1 (h2 p n' r K X O S j b e q I' I'' hc).2
    (h3 p n' r K X O S j b e q I' I'' hc) (h4 p n' r K X O S j b e q I' I'' hc)
  exact ⟨P, hP, hPe.trans (h1 p n' r K X O S j b e q I' I'' hc).symm⟩

end Formalism.MainNotions.SelectionLemmas.Pf
