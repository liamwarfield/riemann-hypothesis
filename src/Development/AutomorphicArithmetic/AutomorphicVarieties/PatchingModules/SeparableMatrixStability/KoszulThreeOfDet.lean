module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.OdComm
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem comm_of_sep {K V : Type} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f g h : Module.End K V) (hs : f.charpoly.Separable)
    (hg : Commute f g) (hh : Commute f h) : g * h = h * g := by
  classical
  have key : ∀ μ : K, ∀ x ∈ f.maxGenEigenspace μ, (g * h) x = (h * g) x := by
    intro μ x hx
    have hd : Module.finrank K (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hs μ
    obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hd
    have hgW := Module.End.mapsTo_maxGenEigenspace_of_comm hg μ
    have hhW := Module.End.mapsTo_maxGenEigenspace_of_comm hh μ
    obtain ⟨a, ha⟩ := hv ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hv ⟨g (v : V), hgW v.2⟩
    obtain ⟨c, hc⟩ := hv ⟨h (v : V), hhW v.2⟩
    have ha' : a • (v : V) = x := congrArg Subtype.val ha
    have hb' : b • (v : V) = g v := congrArg Subtype.val hb
    have hc' : c • (v : V) = h v := congrArg Subtype.val hc
    rw [← ha', Module.End.mul_apply, Module.End.mul_apply, map_smul, map_smul, map_smul, map_smul,
      ← hb', ← hc', map_smul, map_smul, ← hb', ← hc', smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hker : ∀ μ, f.maxGenEigenspace μ ≤ LinearMap.ker (g * h - h * g) := by
    intro μ x hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact key μ x hx
  have htop : LinearMap.ker (g * h - h * g) = ⊤ := by
    rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top f]
    exact iSup_le hker
  exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp htop)

private theorem mat_comm_of_sep {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (P Z E : Matrix (Fin n) (Fin n) K) (hs : P.charpoly.Separable)
    (hg : P * Z = Z * P) (hh : P * E = E * P) : Z * E = E * Z := by
  let φ := (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K))
  have hc : (φ P).charpoly = P.charpoly := Matrix.charpoly_toLin' P
  have e := comm_of_sep (φ P) (φ Z) (φ E) (by rw [hc]; exact hs)
    (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hg])
    (by rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hh])
  apply φ.injective
  rw [map_mul, map_mul]
  exact e

theorem UpperTheory.V.Pa.od_comm :
    ∀ (A : Type) [CommRing A] [IsDomain A] (n a : ℕ) (P Z : Matrix (Fin n) (Fin n) A) (al : Fin n → A), P ∈ Ev A A n a → Z ∈ Od A A n a → Function.Injective al → P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → P * Z = Z * P → Z = 0 := by
  intro A _ _ n a P Z al hP hZ hal hchar hPZ
  classical
  have hP' : ∀ i j : Fin n, ¬((i : ℕ) < a ↔ (j : ℕ) < a) → P i j = 0 := by
    intro i j h
    have := (hP i j).2 h
    simpa using this
  have hZ' : ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j = 0 := by
    intro i j h
    have := (hZ i j).1 h
    simpa using this
  let e : Fin n → A := fun i => if (i : ℕ) < a then 1 else 0
  have hPE : P * Matrix.diagonal e = Matrix.diagonal e * P := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · simp [e, hi, hj]
    · simp [e, hi, hj, hP' i j (by simp [hi, hj])]
    · simp [e, hi, hj, hP' i j (by simp [hi, hj])]
    · simp [e, hi, hj]
  let K := AlgebraicClosure (FractionRing A)
  let ι : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hι : Function.Injective ι :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  have hs : (P.map ι).charpoly.Separable := by
    rw [Matrix.charpoly_map, hchar, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact Polynomial.separable_prod_X_sub_C_iff.mpr (hι.comp hal)
  have h1 : P.map ι * Z.map ι = Z.map ι * P.map ι := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPZ]
  have h2 : P.map ι * (Matrix.diagonal e).map ι = (Matrix.diagonal e).map ι * P.map ι := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hPE]
  have h3 := mat_comm_of_sep (P.map ι) (Z.map ι) ((Matrix.diagonal e).map ι) hs h1 h2
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h3
  have h4 : Z * Matrix.diagonal e = Matrix.diagonal e * Z := Matrix.map_injective hι h3
  ext i j
  have h5 := congrFun (congrFun h4 i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h5
  rw [Matrix.zero_apply]
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
  · exact hZ' i j (by simp [hi, hj])
  · simp only [e, hi, hj, ↓reduceIte, mul_one, mul_zero, one_mul, zero_mul] at h5
    exact h5.symm
  · simp only [e, hi, hj, ↓reduceIte, mul_one, mul_zero, one_mul, zero_mul] at h5
    exact h5
  · exact hZ' i j (by simp [hi, hj])
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocKer
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem closed_zero {Γ K : Type} [TopologicalSpace Γ] [Field K] {f : Γ → PowerSeries K}
    (hf : AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) f) : IsClosed {g | f g = 0} := by
  have hset : {g | f g = 0} = ⋂ N : ℕ,
      {g | Ideal.Quotient.mk ((Ideal.span {(PowerSeries.X : PowerSeries K)}) ^ N) (f g) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · intro h N
      rw [h]
      exact dvd_zero _
    · intro h
      ext n
      have := (PowerSeries.X_pow_dvd_iff).1 (h (n + 1)) n (Nat.lt_succ_self n)
      simpa using this
  rw [hset]
  exact isClosed_iInter fun N => (hf N).isClosed_fiber 0

theorem UpperTheory.V.Pa.coc_ker :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (s : Set G.G₀) (z : G.G₀ → Matrix (Fin n) (Fin n) x.A), h.p.ker ≤ (Subgroup.normalClosure (Subtype.val '' s)).topologicalClosure → (∀ a ∈ s, h.p₀ a = 1 ∧ z a = 0) → z ∈ SelM h x x.A → ∃ y : G0.G₀ → Matrix (Fin n) (Fin n) x.A, ∀ g, y (h.p₀ g) = z g := by
  intro l _ L G G0 h n x s z hker hs hz
  obtain ⟨-, hcont, hcoc, hconj, -, -⟩ := hz
  have coc : ∀ g k : G.G₀,
      z (g * k) = z g + x.ρX x.A (h.p₀ g) * z k * x.ρX x.A (h.p₀ g⁻¹) := hcoc
  have hρ1 : ∀ g : G.G₀, h.p₀ g = 1 → x.ρX x.A (h.p₀ g) = 1 := by
    intro g hg
    rw [hg]
    simp [NP.ρX]
  have hz1 : z 1 = 0 := by
    have e := coc 1 1
    rw [hρ1 1 (map_one _), inv_one, hρ1 1 (map_one _), one_mul, mul_one] at e
    simpa using e
  have hR : ∀ g k : G.G₀, z k = 0 → z (g * k) = z g := by
    intro g k hk
    rw [coc, hk]
    simp
  let H : Subgroup G.G₀ :=
    { carrier := {k | h.p₀ k = 1 ∧ z k = 0}
      one_mem' := ⟨map_one _, hz1⟩
      mul_mem' := by
        rintro a b ⟨ha, za⟩ ⟨hb, zb⟩
        refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
        rw [hR a b zb, za]
      inv_mem' := by
        rintro a ⟨ha, za⟩
        refine ⟨by rw [map_inv, ha, inv_one], ?_⟩
        have e := hR a⁻¹ a za
        rw [inv_mul_cancel, hz1] at e
        exact e.symm }
  have hHconj : ∀ g k : G.G₀, k ∈ H → g * k * g⁻¹ ∈ H := by
    rintro g k ⟨hk1, hk2⟩
    refine ⟨by rw [map_mul, map_mul, hk1, mul_one, map_inv, mul_inv_cancel], ?_⟩
    have hkg : z (k * g⁻¹) = z g⁻¹ := by
      rw [coc, hk2, hρ1 k hk1]
      have : h.p₀ k⁻¹ = 1 := by rw [map_inv, hk1, inv_one]
      rw [hρ1 _ this]
      simp
    rw [mul_assoc, coc, hkg, ← coc, mul_inv_cancel, hz1]
  have hHc : ∀ k : G.G₀, k ∈ H → G.frame.conj k ∈ H := by
    rintro k ⟨hk1, hk2⟩
    refine ⟨?_, ?_⟩
    · rw [h.p₀_conj, hk1, map_one]
    · rw [hconj, hk2]
      simp
  let N : Subgroup G.Γ := H.map G.η.ker.subtype
  have hN : N.Normal := by
    constructor
    intro m hm γ
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hm
    rcases Int.units_eq_one_or (G.η γ) with hγ | hγ
    · have e : γ * (k : G.Γ) * γ⁻¹ = (((⟨γ, hγ⟩ : G.G₀) * k * (⟨γ, hγ⟩ : G.G₀)⁻¹ : G.G₀) : G.Γ) := rfl
      exact Subgroup.mem_map.2 ⟨_, hHconj _ _ hk, e.symm⟩
    · have hg : G.c⁻¹ * γ ∈ G.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, G.η_c, hγ]
        rfl
      let g : G.G₀ := ⟨G.c⁻¹ * γ, hg⟩
      have e : γ * (k : G.Γ) * γ⁻¹ = ((G.frame.conj (g * k * g⁻¹) : G.G₀) : G.Γ) := by
        show γ * (k : G.Γ) * γ⁻¹ = G.c * ((G.c⁻¹ * γ) * (k : G.Γ) * (G.c⁻¹ * γ)⁻¹) * G.c⁻¹
        group
      exact Subgroup.mem_map.2 ⟨_, hHc _ (hHconj _ _ hk), e.symm⟩
  have hHclosed : IsClosed (H : Set G.G₀) := by
    have e1 : (H : Set G.G₀) = {k | h.p₀ k = 1} ∩ ⋂ i, ⋂ j, {k | z k i j = 0} := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i j => by rw [h2]; rfl⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Matrix.ext fun i j => h2 i j⟩
    rw [e1]
    exact IsClosed.inter ((isClosed_singleton (x := (1 : G0.G₀))).preimage h.p₀_cont)
      (isClosed_iInter fun i => isClosed_iInter fun j => closed_zero (hcont i j))
  have hNclosed : IsClosed (N : Set G.Γ) := by
    show IsClosed (Subtype.val '' (H : Set G.G₀))
    exact hHclosed.trans (Subgroup.isClosed_of_isOpen _ G.η_open)
  have hsN : Subtype.val '' s ⊆ (N : Set G.Γ) := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.2 ⟨a, ⟨(hs a ha).1, (hs a ha).2⟩, rfl⟩
  have hkerN : h.p.ker ≤ N :=
    hker.trans (Subgroup.topologicalClosure_minimal _
      (Subgroup.normalClosure_le_normal (N := N) hsN) hNclosed)
  have hfac : ∀ g g' : G.G₀, h.p₀ g = h.p₀ g' → z g = z g' := by
    intro g g' e
    have h1 : h.p₀ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
    have h2 : ((g⁻¹ * g' : G.G₀) : G.Γ) ∈ h.p.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
    obtain ⟨k, hk, hk'⟩ := Subgroup.mem_map.1 (hkerN h2)
    have hkk : k = g⁻¹ * g' := Subtype.ext hk'
    rw [hkk] at hk
    have e2 := hR g _ hk.2
    rw [mul_inv_cancel_left] at e2
    exact e2.symm
  exact ⟨fun g0 => z (Classical.choose (h.p₀_surj g0)),
    fun g => hfac _ _ (Classical.choose_spec (h.p₀_surj (h.p₀ g)))⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.KerOo
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem isOpen_map_of_ker_le {P Z : Type} [Group P] [TopologicalSpace P] [CompactSpace P]
    [Group Z] [TopologicalSpace Z] [T2Space Z] (f : P →* Z) (hf : Continuous f) (hs : Function.Surjective f)
    (V : Subgroup P) (hV : IsOpen (V : Set P)) (hk : f.ker ≤ V) : IsOpen (V.map f : Set Z) := by
  rw [← (hf.isClosedMap.isQuotientMap hf hs).isOpen_preimage]
  have : f ⁻¹' (V.map f : Set Z) = V := by
    rw [← Subgroup.coe_comap, Subgroup.comap_map_eq_self hk]
  rw [this]; exact hV

theorem UpperTheory.V.Pa.ker_oo :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T), T.ProL → Λ.h.p.ker ≤ (Subgroup.normalClosure (Set.range fun j => (Λ.ta j : Λ.G.Γ))).topologicalClosure := by
  intro l _ L G0 T Λ hT x hx
  set K := (Subgroup.normalClosure (Set.range fun j => (Λ.ta j : Λ.G.Γ))).topologicalClosure with hK
  haveI : K.Normal := Subgroup.is_normal_topologicalClosure _
  refine (totallyDisconnected_quot Λ.G.Γ K (Subgroup.isClosed_topologicalClosure _)).2 x fun O => ?_
  haveI := O.isNormal'
  set W : Subgroup Λ.G.Γ := K ⊔ O.toSubgroup with hW
  haveI hWn : W.Normal := Subgroup.sup_normal _ _
  have hWo : IsOpen (W : Set Λ.G.Γ) := Subgroup.isOpen_mono (le_sup_right : O.toSubgroup ≤ W) O.isOpen'
  have hta : ∀ j, (Λ.ta j : Λ.G.Γ) ∈ W := fun j =>
    Subgroup.mem_sup_left (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨j, rfl⟩))
  let V : OpenNormalSubgroup Λ.Ph :=
    { toSubgroup := W.comap Λ.πo, isOpen' := hWo.preimage Λ.πo_cont, isNormal' := hWn.comap _ }
  have hVn : V.toSubgroup.Normal := V.isNormal'
  have hVo : IsOpen (V.toSubgroup : Set Λ.Ph) := V.isOpen'
  have hko : Λ.πo.ker ≤ V.toSubgroup := fun g hg => by
    show Λ.πo g ∈ W
    rw [MonoidHom.mem_ker.1 hg]; exact W.one_mem
  have hPh : TopFG Λ.Ph := by
    obtain ⟨s, hs⟩ := Λ.fg
    exact ⟨s, s.finite_toSet, (topGen_iff _).2 hs⟩
  have hG0 : TopFG G0.Γ := (TopFG.subgroup_quot Λ.Ph hPh).2 G0.Γ (Λ.h.p.comp Λ.πo) (Λ.h.cont.comp Λ.πo_cont)
    (Λ.h.surj.comp Λ.πo_surj)
  have hidx : V.toSubgroup.index ≠ 0 := by
    haveI : Finite (Λ.Ph ⧸ V.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ hVo
    exact Subgroup.index_ne_zero_of_finite
  have hfin := (finite_hom_of_topFG G0.Γ hG0).2.2 _ hidx
  have hall : ∀ᶠ N in (Λ.U : Filter ℕ), ∀ A ∈ {H : Subgroup G0.Γ | IsOpen (H : Set G0.Γ) ∧ H.index = V.toSubgroup.index},
      A.Normal → ∀ g, (T.h N).p (Λ.π N g) * (Λ.h.p (Λ.πo g))⁻¹ ∈ A := by
    rw [hfin.eventually_all]
    intro A hA
    by_cases hn : A.Normal
    · exact (Λ.p_lim { toSubgroup := A, isOpen' := hA.1, isNormal' := hn }).mono fun N h _ => h
    · exact Eventually.of_forall fun N h => absurd h hn
  obtain ⟨N, h1, h2, h3⟩ := ((Λ.ker_lim V).and ((Λ.ta_lim V).and hall)).exists
  have hkN : (Λ.π N).ker ≤ V.toSubgroup := le_sup_left.trans (h1.le.trans (sup_le hko le_rfl))
  haveI hVNn : (V.toSubgroup.map (Λ.π N)).Normal := hVn.map _ (Λ.π_surj N)
  have hVNo := isOpen_map_of_ker_le (Λ.π N) (Λ.π_cont N) (Λ.π_surj N) _ hVo hkN
  have hkh : (T.h N).p.ker ≤ V.toSubgroup.map (Λ.π N) := by
    refine (T.ker_le N).trans (Subgroup.topologicalClosure_minimal _ ?_ (Subgroup.isClosed_of_isOpen _ hVNo))
    rw [hT.2 N, sup_bot_eq]
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨j, rfl⟩
    obtain ⟨g, g', hg, hg', hgg⟩ := h2 j
    have hg'V : g' ∈ V.toSubgroup := by
      show Λ.πo g' ∈ W
      rw [hg']; exact hta j
    refine ⟨g, ?_, hg⟩
    have := mul_mem hg'V (inv_mem hgg)
    simpa using this
  let f : Λ.Ph →* G0.Γ := (T.h N).p.comp (Λ.π N)
  have hfs : Function.Surjective f := (T.h N).surj.comp (Λ.π_surj N)
  have hfk : f.ker ≤ V.toSubgroup := fun g hg => by
    rw [← Subgroup.comap_map_eq_self hkN]
    exact hkh hg
  have hAo := isOpen_map_of_ker_le f ((T.h N).cont.comp (Λ.π_cont N)) hfs _ hVo hfk
  have hAi : (V.toSubgroup.map f).index = V.toSubgroup.index := by
    rw [← Subgroup.index_comap_of_surjective _ hfs, Subgroup.comap_map_eq_self hfk]
  obtain ⟨g, rfl⟩ := Λ.πo_surj x
  have h4 := h3 _ ⟨hAo, hAi⟩ (hVn.map _ hfs) g
  rw [MonoidHom.mem_ker.1 hx, inv_one, mul_one] at h4
  have h5 : g ∈ (V.toSubgroup.map f).comap f := h4
  rw [Subgroup.comap_map_eq_self hfk] at h5
  exact h5
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.koszulThree_of_det :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (al : Fin T.q → Fin n → x.A), T.ProL → T.Eig x al → K3 Λ.h k := by
  intro l _ L G0 T Λ n x k al hP hE
  intro z hz
  have hρ : ∀ g, x.ρX x.A g = mat x.ρ g := by
    intro g
    ext i j
    simp [NP.ρX]
  have hzero : ∀ j, z (Λ.ta j) = 0 := by
    intro j
    have hc := Λ.comm j
    have h1 := hz.2.2.1 (Λ.ph j) (Λ.ta j)
    have h2 := hz.2.2.1 (Λ.ta j) (Λ.ph j)
    rw [hc] at h1
    simp only [hρ, map_inv, Λ.p_ta, Λ.p_ph, map_one, inv_one, one_mul, mul_one] at h1 h2
    rw [h2] at h1
    have h3 : z (Λ.ta j) = mat x.ρ (T.sg j) * z (Λ.ta j) * mat x.ρ (T.sg j)⁻¹ := by
      have := h1
      rw [add_comm (z (Λ.ta j))] at this
      exact add_left_cancel this
    have hPZ : mat x.ρ (T.sg j) * z (Λ.ta j) = z (Λ.ta j) * mat x.ρ (T.sg j) := by
      conv_rhs => rw [h3]
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    exact od_comm x.A n x.a (mat x.ρ (T.sg j)) (z (Λ.ta j)) (al j) (x.blk _) (hz.1 _)
      (hE j).1 (hE j).2 hPZ
  obtain ⟨y, hy⟩ := coc_ker l L Λ.G G0 Λ.h n x (Set.range Λ.ta) z
    (by rw [← Set.range_comp]; exact ker_oo l L G0 T Λ hP)
    (by
      rintro a ⟨j, rfl⟩
      exact ⟨Λ.p_ta j, hzero j⟩)
    hz
  have hzy : (fun g => y (Λ.h.p₀ g)) = z := funext hy
  have hy' : y ∈ SelZ G0.frame x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    rw [← Glob.Hom.sel_iff Λ.h, hzy]
    exact hz
  obtain ⟨s, c, hsc⟩ := k.gen y hy'
  refine ⟨s, c, ?_⟩
  have hb := (Glob.Hom.bd_iff Λ.h (x.ρX x.A) (Od x.A x.A n x.a) _).mpr hsc
  show _ ∈ Bd Λ.G.frame (fun g => x.ρX x.A (Λ.h.p₀ g)) (Od x.A x.A n x.a)
  convert hb using 1
  funext g
  simp [hy]
