module

public import Development.AutomorphicArithmetic.DivisorFrames.ExistsIrreducibleSubrepHeckeEigenOfInvariantForm
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsOpenIsCompactSubgroupFiniteAdelicUnitary

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupIrreducibleOfAdmissibleUnitary
theorem UpperTheory.mem_iSup_irreducible_of_admissible_unitary :
    ∀ (H W : Type) [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), (∀ v, B v v = 0 → v = 0) → (∀ g u v, B (ρ g u) (ρ g v) = B u v) → (∀ v, ∃ K : Subgroup H, (∀ k ∈ K, ρ k v = v) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K) ∧ ∀ w, (Set.range fun k : K => ρ k w).Finite) → ∀ x : W, x ∈ ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1 := by
  intro H W _ _ _ ρ B hdef hinv hadm x
  classical
  set S : Submodule ℂ W := ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1 with hS
  have hSle : ∀ U : Submodule ℂ W, U ≠ ⊥ → (∀ g, ∀ u ∈ U, ρ g u ∈ U) →
      (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) → U ≤ S := by
    intro U h1 h2 h3
    exact le_iSup (fun U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U} => U.1) ⟨U, h1, h2, h3⟩
  have hSinv : ∀ g, ∀ u ∈ S, ρ g u ∈ S := by
    intro g u hu
    have hle : S ≤ S.comap (ρ g) := by
      refine iSup_le ?_
      rintro ⟨U, h1, h2, h3⟩ v hv
      exact hSle U h1 h2 h3 (h2 g v hv)
    exact hle hu
  let Z : Subrepresentation ρ := ⟨S, fun g v hv => hSinv g v hv⟩
  let O : Submodule ℂ W := ⨅ z : S, LinearMap.ker (B (z : W))
  have memO : ∀ w, w ∈ O ↔ ∀ z ∈ S, B z w = 0 := by
    intro w
    simp [O, Submodule.mem_iInf]
  let Y : Subrepresentation ρ := ⟨O, fun g v hv =>
    (memO _).2 (GlobalTheory.UnitarySemisimple.orth_stable ρ B hinv Z v ((memO _).1 hv) g)⟩
  obtain ⟨t, htS, ht⟩ := GlobalTheory.UnitarySemisimple.exists_compl_proj ρ B hdef hinv hadm Z x
  by_cases h0 : x - t = 0
  · rw [sub_eq_zero.1 h0]
    exact htS
  exfalso
  let σ : Representation ℂ H O := Y.toRepresentation
  have hσ : ∀ g (v : O), ((σ g v : O) : W) = ρ g v := fun _ _ => rfl
  let B' : O →ₗ⋆[ℂ] O →ₗ[ℂ] ℂ := (B.comp O.subtype).compl₂ O.subtype
  have hB' : ∀ u v : O, B' u v = B u v := fun _ _ => rfl
  have hadm' : ∀ v : O, ∃ K : Subgroup H, (∀ k ∈ K, σ k v = v) ∧
      FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K) ∧ ∀ w, (Set.range fun k : K => σ k w).Finite := by
    intro v
    obtain ⟨K, h1, h2, h3⟩ := hadm v
    refine ⟨K, fun k hk => Subtype.ext (h1 k hk), ?_, fun w => ?_⟩
    · let f : GlobalTheory.PRep.fixed σ K →ₗ[ℂ] GlobalTheory.PRep.fixed ρ K :=
        (O.subtype.comp (GlobalTheory.PRep.fixed σ K).subtype).codRestrict _ (by
          intro u k
          exact congrArg Subtype.val (u.2 k))
      refine Module.Finite.of_injective f ?_
      intro a b hab
      have hab' : ((f a : GlobalTheory.PRep.fixed ρ K) : W) = ((f b : GlobalTheory.PRep.fixed ρ K) : W) := by rw [hab]
      exact Subtype.ext (Subtype.ext hab')
    · refine Set.Finite.of_finite_image (f := Subtype.val) ((h3 w).subset ?_) Subtype.val_injective.injOn
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
  obtain ⟨U, hU, hirr, f, hfU, hf0, -⟩ := UpperTheory.exists_irreducible_subrep_hecke_eigen_of_invariant_form H O σ B'
    (fun v hv => Subtype.ext (hdef _ hv)) (fun g u v => hinv g u v) hadm'
    ⟨x - t, (memO _).2 ht⟩ (fun h => h0 (congrArg Subtype.val h))
  have hf0' : (f : W) ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hfU' : (f : W) ∈ U.map O.subtype := ⟨f, hfU, rfl⟩
  have hle : U.map O.subtype ≤ S := by
    refine hSle _ (fun h => hf0' (by simpa [h] using hfU')) ?_ ?_
    · rintro g _ ⟨u, hu, rfl⟩
      exact ⟨σ g u, hU g u hu, rfl⟩
    · intro N hN hNinv
      have hNO : N ≤ O := hN.trans (Submodule.map_subtype_le _ _)
      have hmc : (N.comap O.subtype).map O.subtype = N := by
        rw [Submodule.map_comap_subtype, inf_eq_right.2 hNO]
      have hle' : N.comap O.subtype ≤ U := by
        intro u hu
        obtain ⟨w, hw, hwu⟩ := hN hu
        have : w = u := Subtype.ext hwu
        exact this ▸ hw
      rcases hirr _ hle' (fun g u hu => hNinv g u hu) with h | h
      · left
        rw [← hmc, h, Submodule.map_bot]
      · right
        rw [← hmc, h]
  exact hf0' (hdef _ ((memO _).1 f.2 _ (hle hfU')))
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AutTranslate
private theorem UpperTheory.Reformulated.B.Gr38.matrix_comm {R₁ R₂ m : Type} [CommRing R₁] [CommRing R₂] [Fintype m]
    [DecidableEq m] (X Y : Matrix m m (R₁ × R₂))
    (hX : X.map (RingHom.snd R₁ R₂) = 1) (hY : Y.map (RingHom.fst R₁ R₂) = 1) : X * Y = Y * X := by
  have hf : (X * Y).map (RingHom.fst R₁ R₂) = (Y * X).map (RingHom.fst R₁ R₂) := by
    rw [Matrix.map_mul, Matrix.map_mul, hY, mul_one, one_mul]
  have hs : (X * Y).map (RingHom.snd R₁ R₂) = (Y * X).map (RingHom.snd R₁ R₂) := by
    rw [Matrix.map_mul, Matrix.map_mul, hX, mul_one, one_mul]
  exact Matrix.ext fun i j =>
    Prod.ext (congr_fun (congr_fun hf i) j) (congr_fun (congr_fun hs i) j)

private theorem UpperTheory.Reformulated.B.Gr38.inf_fin_comm {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {n : ℕ} (x : ↥(GlobalTheory.UnitaryBC.infU E n))
    (k : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))) :
    (x : ↥(GlobalTheory.UnitaryBC.UA E n)) * (k : ↥(GlobalTheory.UnitaryBC.UA E n)) =
      (k : ↥(GlobalTheory.UnitaryBC.UA E n)) * (x : ↥(GlobalTheory.UnitaryBC.UA E n)) := by
  apply Subtype.ext
  apply Units.ext
  let X : Matrix (Fin n) (Fin n) (GlobalTheory.CuspRep.Ad E) :=
    (((x : ↥(GlobalTheory.UnitaryBC.UA E n)) : GlobalTheory.CuspRep.GA E n) : Matrix _ _ _)
  let Y : Matrix (Fin n) (Fin n) (GlobalTheory.CuspRep.Ad E) :=
    (((k : ↥(GlobalTheory.UnitaryBC.UA E n)) : GlobalTheory.CuspRep.GA E n) : Matrix _ _ _)
  have hx : X.map (GlobalTheory.CuspRep.pFin E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 x.2)
  have hk : Y.map (GlobalTheory.CuspRep.pInf E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 k.2)
  have hk' : Y.map (RingHom.fst (NumberField.InfiniteAdeleRing E) (GlobalTheory.CuspRep.Af E)) = 1 := by
    have h1 : Y.map (RingHom.fst (NumberField.InfiniteAdeleRing E) (GlobalTheory.CuspRep.Af E)) =
        (Y.map (GlobalTheory.CuspRep.pInf E)).map (GlobalTheory.CuspRep.infEq E) := by
      ext i j : 2
      exact ((GlobalTheory.CuspRep.infEq E).apply_symm_apply _).symm
    rw [h1, hk]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact UpperTheory.Reformulated.B.Gr38.matrix_comm (R₁ := NumberField.InfiniteAdeleRing E)
    (R₂ := GlobalTheory.CuspRep.Af E) X Y hx hk'

private theorem UpperTheory.Reformulated.B.Gr38.ru_comm {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {n : ℕ} (x : ↥(GlobalTheory.UnitaryBC.infU E n))
    (k : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))) (φ : ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) :
    GlobalTheory.UnitaryBC.RU E n (x : ↥(GlobalTheory.UnitaryBC.UA E n)) (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ) =
      GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (GlobalTheory.UnitaryBC.RU E n (x : ↥(GlobalTheory.UnitaryBC.UA E n)) φ) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    UpperTheory.Reformulated.B.Gr38.inf_fin_comm]

private theorem UpperTheory.Reformulated.B.Gr38.conj_fix {G V : Type} [Group G] [AddCommGroup V] [_root_.Module ℂ V]
    (R : Representation ℂ G V) (a k : G) (φ : V) :
    R (k⁻¹ * a * k) φ = φ ↔ R a (R k φ) = R k φ := by
  have h1 : ∀ v, R k⁻¹ (R k v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have h2 : ∀ v, R k (R k⁻¹ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [map_mul, map_mul]
  simp only [Module.End.mul_apply]
  constructor
  · intro h
    have := congrArg (R k) h
    rwa [h2] at this
  · intro h
    rw [h, h1]

private theorem UpperTheory.Reformulated.B.Gr38.aut_translate {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {n : ℕ} (k : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)))
    {φ : ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ} (h : φ ∈ GlobalTheory.DefU.autU E n) :
    GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ ∈ GlobalTheory.DefU.autU E n := by
  obtain ⟨hc, hr, ho, hf⟩ := (h : GlobalTheory.UnitaryBC.IsAutFormU φ)
  refine (GlobalTheory.UnitaryBC.IsAutFormU.mk ?_ ?_ ?_ ?_ :
    GlobalTheory.UnitaryBC.IsAutFormU (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ))
  · exact hc.comp (continuous_mul_const (k : ↥(GlobalTheory.UnitaryBC.UA E n)))
  · intro γ hγ g
    have := hr γ hγ (g * k)
    rw [← mul_assoc] at this
    exact this
  · have hs : {k' : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) |
        GlobalTheory.UnitaryBC.RU E n (k' : ↥(GlobalTheory.UnitaryBC.UA E n))
          (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ) =
            GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ} =
        (fun k' : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) => k⁻¹ * k' * k) ⁻¹'
          {k' : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) |
            GlobalTheory.UnitaryBC.RU E n (k' : ↥(GlobalTheory.UnitaryBC.UA E n)) φ = φ} := by
      ext k'
      exact (UpperTheory.Reformulated.B.Gr38.conj_fix (GlobalTheory.UnitaryBC.RU E n) (k' : ↥(GlobalTheory.UnitaryBC.UA E n))
        (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ).symm
    rw [hs]
    exact ho.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · have hs : Submodule.span ℂ (Set.range fun x : ↥(GlobalTheory.UnitaryBC.infU E n) =>
        GlobalTheory.UnitaryBC.RU E n (x : ↥(GlobalTheory.UnitaryBC.UA E n))
          (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) φ)) =
        (Submodule.span ℂ (Set.range fun x : ↥(GlobalTheory.UnitaryBC.infU E n) =>
          GlobalTheory.UnitaryBC.RU E n (x : ↥(GlobalTheory.UnitaryBC.UA E n)) φ)).map
            (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      congr 2
      funext x
      exact UpperTheory.Reformulated.B.Gr38.ru_comm x k φ
    rw [hs]
    infer_instance

private def UpperTheory.Reformulated.B.Gr38.fixer {G W : Type} [Group G] [AddCommGroup W] [_root_.Module ℂ W]
    (R : Representation ℂ G W) (w : W) : Subgroup G where
  carrier := {g | R g w = w}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h : R a⁻¹ (R a w) = w := by
      rw [← Module.End.mul_apply, ← map_mul]; simp
    rwa [ha] at h

private theorem UpperTheory.Reformulated.B.Gr38.orbit_finite {G W : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup W] [_root_.Module ℂ W] (R : Representation ℂ G W)
    (K : Subgroup G) (hK : IsCompact (K : Set G)) (w : W)
    (hw : IsOpen (UpperTheory.Reformulated.B.Gr38.fixer R w : Set G)) :
    (Set.range fun k : ↥K => R (k : G) w).Finite := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let U : Subgroup ↥K := (UpperTheory.Reformulated.B.Gr38.fixer R w).subgroupOf K
  have hU : IsOpen (U : Set ↥K) := hw.preimage continuous_subtype_val
  haveI : Finite (↥K ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  refine (Set.finite_range (fun c : ↥K ⧸ U => R ((c.out : ↥K) : G) w)).subset ?_
  rintro _ ⟨k, rfl⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U k
  refine ⟨(k : ↥K ⧸ U), ?_⟩
  have hfix : R ((h : ↥K) : G) w = w := h.2
  simp only [hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hfix]

private theorem UpperTheory.Reformulated.B.Gr38.stab_open {E : Type} [Field E] [NumberField E]
    [NumberField.IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S] [_root_.Module ℂ S]
    [FiniteDimensional ℂ S] (f : S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ)
    (hf : ∀ v, f v ∈ GlobalTheory.DefU.autU E n) :
    IsOpen {k : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) |
      ∀ v, GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (f v) = f v} := by
  let b := Module.finBasis ℂ S
  have hs : {k : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) |
      ∀ v, GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (f v) = f v} =
      ⋂ i, {k : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) |
        GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (f (b i)) = f (b i)} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h i => h _, fun h v => ?_⟩
    have : (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n))) ∘ₗ f = f := b.ext h
    exact LinearMap.congr_fun this v
  rw [hs]
  refine isOpen_iInter_of_finite fun i => ?_
  obtain ⟨_, _, ho, _⟩ := (hf (b i) : GlobalTheory.UnitaryBC.IsAutFormU (f (b i)))
  exact ho

noncomputable def UpperTheory.Reformulated.B.Gr38.eqForms :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          [inst_2 : NumberField.IsCMField E] →
            {n : ℕ} →
              {S : Type} →
                [inst_3 : AddCommGroup S] →
                  [inst_4 : _root_.Module ℂ S] →
                    Representation ℂ (↥(GlobalTheory.UnitaryBC.infU E n)) S → Submodule ℂ (S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) :=
    fun {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S]
        [_root_.Module ℂ S] (ρ : Representation ℂ (↥(GlobalTheory.UnitaryBC.infU E n)) S) ↦
      {
        carrier :=
          {f : S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ |
            (∀ (v : S), (f : S → ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) v ∈ GlobalTheory.DefU.autU E n) ∧
              ∀ (x : ↥(GlobalTheory.UnitaryBC.infU E n)) (v : S),
                (f : S → ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) (((ρ : ↥(GlobalTheory.UnitaryBC.infU E n) → S →ₗ[ℂ] S) x : S → S) v) =
                  ((GlobalTheory.UnitaryBC.RU E n :
                                   ↥(GlobalTheory.UnitaryBC.UA E n) → (↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ)
                                 (↑x : ↥(GlobalTheory.UnitaryBC.UA E n)) :
                      (↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) → ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ)
                    ((f : S → ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) v)},
        add_mem' := (by
          intro f g hf hg
          refine ⟨fun v => (GlobalTheory.DefU.autU E n).add_mem (hf.1 v) (hg.1 v), fun x v => ?_⟩
          simp only [LinearMap.add_apply, hf.2 x v, hg.2 x v, map_add (f := _)]),
        zero_mem' := (by
          refine ⟨fun v => (GlobalTheory.DefU.autU E n).zero_mem, fun x v => ?_⟩
          simp only [LinearMap.zero_apply, map_zero]),
        smul_mem' := (by
          intro c f hf
          refine ⟨fun v => (GlobalTheory.DefU.autU E n).smul_mem c (hf.1 v), fun x v => ?_⟩
          simp only [LinearMap.smul_apply, hf.2 x v, map_smul]) : Submodule ℂ (S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) }

noncomputable def UpperTheory.Reformulated.B.Gr38.eqRep :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : NumberField E] →
          [inst_2 : NumberField.IsCMField E] →
            {n : ℕ} →
              {S : Type} →
                [inst_3 : AddCommGroup S] →
                  [inst_4 : _root_.Module ℂ S] →
                    (ρ : Representation ℂ (↥(GlobalTheory.UnitaryBC.infU E n)) S) →
                      Representation ℂ ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) :=
    fun {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S]
        [_root_.Module ℂ S] (ρ : Representation ℂ (↥(GlobalTheory.UnitaryBC.infU E n)) S) ↦
      {
        toFun := fun (k : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))) ↦
          ((LinearMap.llcomp ℂ S (↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) (↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) :
                  ((↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) →
                    (S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) →ₗ[ℂ] S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ)
                ((GlobalTheory.UnitaryBC.RU E n :
                    ↥(GlobalTheory.UnitaryBC.UA E n) → (↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ)
                  (↑k : ↥(GlobalTheory.UnitaryBC.UA E n)))).restrict
            (by
              intro g hg
              refine ⟨fun v => UpperTheory.Reformulated.B.Gr38.aut_translate k (hg.1 v), fun x v => ?_⟩
              show GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (g (ρ x v)) =
                GlobalTheory.UnitaryBC.RU E n (x : ↥(GlobalTheory.UnitaryBC.UA E n))
                  (GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (g v))
              rw [hg.2 x v, UpperTheory.Reformulated.B.Gr38.ru_comm]),
        map_one' := (by
          apply LinearMap.ext
          intro g
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          show GlobalTheory.UnitaryBC.RU E n ((1 : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))) : ↥(GlobalTheory.UnitaryBC.UA E n)) (g.1 v) = g.1 v
          simp),
        map_mul' := (by
          intro k l
          apply LinearMap.ext
          intro g
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          show GlobalTheory.UnitaryBC.RU E n ((k * l : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))) : ↥(GlobalTheory.UnitaryBC.UA E n)) (g.1 v) =
            GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n))
              (GlobalTheory.UnitaryBC.RU E n (l : ↥(GlobalTheory.UnitaryBC.UA E n)) (g.1 v))
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]) :
        ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) →* ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) →ₗ[ℂ] ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) }

theorem UpperTheory.Reformulated.B.Gr38.eqRep_adm :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {n : ℕ} {S : Type}
      [inst_3 : AddCommGroup S] [inst_4 : _root_.Module ℂ S] [FiniteDimensional ℂ S]
      (ρ : Representation ℂ (↥(GlobalTheory.UnitaryBC.infU E n)) S) (f : ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ)),
      ∃ (K : Subgroup ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))),
        (∀ k ∈ K,
            ((UpperTheory.Reformulated.B.Gr38.eqRep ρ :
                            ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) → ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) →ₗ[ℂ] ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ))
                          k :
                  ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) → ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ))
                f =
              f) ∧
          FiniteDimensional ℂ ↥(GlobalTheory.PRep.fixed (UpperTheory.Reformulated.B.Gr38.eqRep ρ) K) ∧
            ∀ (w : ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ)),
              (Set.range fun (k : ↥K) ↦
                  ((UpperTheory.Reformulated.B.Gr38.eqRep ρ :
                                ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) → ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) →ₗ[ℂ] ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ))
                        (↑k : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))) :
                      ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ) → ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ))
                    w).Finite := by
  intro E _ _ _ n S _ _ _ ρ f
  obtain ⟨K0, hK0o, hK0c⟩ := UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E n
  have hopen : ∀ w : ↥(UpperTheory.Reformulated.B.Gr38.eqForms ρ),
      IsOpen (UpperTheory.Reformulated.B.Gr38.fixer (UpperTheory.Reformulated.B.Gr38.eqRep ρ) w : Set ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))) := by
    intro w
    have hs : (UpperTheory.Reformulated.B.Gr38.fixer (UpperTheory.Reformulated.B.Gr38.eqRep ρ) w : Set ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))) =
        {k : ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) |
          ∀ v, GlobalTheory.UnitaryBC.RU E n (k : ↥(GlobalTheory.UnitaryBC.UA E n)) (w.1 v) = w.1 v} := by
      ext k
      constructor
      · intro h v
        exact LinearMap.congr_fun (congrArg Subtype.val (show UpperTheory.Reformulated.B.Gr38.eqRep ρ k w = w from h)) v
      · intro h
        show UpperTheory.Reformulated.B.Gr38.eqRep ρ k w = w
        exact Subtype.ext (LinearMap.ext h)
    rw [hs]
    exact UpperTheory.Reformulated.B.Gr38.stab_open w.1 w.2.1
  let K : Subgroup ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n)) :=
    K0 ⊓ UpperTheory.Reformulated.B.Gr38.fixer (UpperTheory.Reformulated.B.Gr38.eqRep ρ) f
  have hKo : IsOpen (K : Set ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))) := hK0o.inter (hopen f)
  have hKc : IsCompact (K : Set ↥(GlobalTheory.UnitaryBC.finU (E := E) (n := n))) :=
    hK0c.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) Set.inter_subset_left
  refine ⟨K, fun k hk => hk.2, ?_, fun w =>
    UpperTheory.Reformulated.B.Gr38.orbit_finite (UpperTheory.Reformulated.B.Gr38.eqRep ρ) K hKc w (hopen w)⟩
  let M : Submodule ℂ (S →ₗ[ℂ] ↥(GlobalTheory.UnitaryBC.UA E n) → ℂ) :=
    (GlobalTheory.PRep.fixed (UpperTheory.Reformulated.B.Gr38.eqRep ρ) K).map (UpperTheory.Reformulated.B.Gr38.eqForms ρ).subtype
  have hM : FiniteDimensional ℂ ↥M := by
    refine UpperTheory.finiteDimensional_automorphicForms_unitary_of_type_level E n S (fun x => ρ x) K hKo M ?_
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨fun v γ hγ g => ?_, fun x v => w.2.2 x v, fun k hk v => ?_⟩
    · obtain ⟨_, hr, _, _⟩ := (w.2.1 v : GlobalTheory.UnitaryBC.IsAutFormU (w.1 v))
      exact hr γ hγ g
    · have h1 : UpperTheory.Reformulated.B.Gr38.eqRep ρ k w = w := by
        have := hw ⟨k, hk⟩
        simpa using this
      exact LinearMap.congr_fun (congrArg Subtype.val h1) v
  exact LinearEquiv.finiteDimensional
    (Submodule.equivMapOfInjective (UpperTheory.Reformulated.B.Gr38.eqForms ρ).subtype
      (Submodule.injective_subtype _) (GlobalTheory.PRep.fixed (UpperTheory.Reformulated.B.Gr38.eqRep ρ) K)).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdmissibleEquivariantFormsRepresentation
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {S : Type} [AddCommGroup S] [Module ℂ S]

private def eqForms (ρ : Representation ℂ (infU E n) S) : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {f | (∀ v, f v ∈ autU E n) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)}
  add_mem' ha hb := ⟨fun v => add_mem (ha.1 v) (hb.1 v), fun x v => by
    rw [LinearMap.add_apply, LinearMap.add_apply, ha.2, hb.2, map_add (f := _)]⟩
  zero_mem' := ⟨fun _ => zero_mem _, fun _ _ => rfl⟩
  smul_mem' c _ ha := ⟨fun v => Submodule.smul_mem _ c (ha.1 v), fun x v => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, ha.2, map_smul]⟩

private noncomputable def eqRep (ρ : Representation ℂ (infU E n) S) : Representation ℂ (finU (E := E) (n := n)) (eqForms ρ) where
  toFun k := (LinearMap.llcomp ℂ _ _ _ (RU E n k)).restrict (p := eqForms ρ) (q := eqForms ρ) fun f h =>
    ⟨fun v => RU_mem_autU _ _ (h.1 v), fun x v => by
      change RU E n k (f (ρ x v)) = RU E n x (RU E n k (f v))
      rw [h.2, RU_RU, RU_RU, fin_mul_inf k.2 x.2]⟩
  map_one' := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g => congrArg (f.1 v) (mul_one g))
  map_mul' a b := LinearMap.ext fun f => Subtype.ext (LinearMap.ext fun v => funext fun g =>
    congrArg (f.1 v) (mul_assoc g a b).symm)

private theorem eqRep_adm [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (f : eqForms ρ) :
    ∃ K : Subgroup (finU (E := E) (n := n)), (∀ k ∈ K, eqRep ρ k f = f) ∧ FiniteDimensional ℂ (GlobalTheory.PRep.fixed (eqRep ρ) K) ∧
      ∀ w, (Set.range fun k : K => eqRep ρ k w).Finite :=
  _root_.UpperTheory.Reformulated.B.Gr38.eqRep_adm ρ f

end

theorem UpperTheory.admissible_equivariantForms_representation :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → B φ φ = 0 → φ = 0) → (∀ x φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n x φ) (RU E n x ψ) = B φ ψ) → ∀ (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ f : S →ₗ[ℂ] (UA E n → ℂ), (∀ v, IsAutFormU (f v)) → (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → ∀ v, f v ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1 := by
  intro E _ _ _ n B hdefB hinv S _ _ _ ρ hsp f hfa hfe v
  classical
  by_cases hv : v = 0
  · rw [hv, map_zero]
    exact zero_mem _
  let ev : eqForms ρ →ₗ[ℂ] (UA E n → ℂ) := LinearMap.applyₗ v ∘ₗ (eqForms ρ).subtype
  let B' : eqForms ρ →ₗ⋆[ℂ] eqForms ρ →ₗ[ℂ] ℂ := (B.compl₂ ev).comp ev
  have hB' : ∀ u w, B' u w = B (u.1 v) (w.1 v) := fun _ _ => rfl
  have hev : ∀ u : eqForms ρ, u.1 v = 0 → u = 0 := fun u hu => by
    have h1 : ∀ T ∈ Submodule.span ℂ (Set.range ρ), u.1 (T v) = 0 := by
      intro T hT
      induction hT using Submodule.span_induction with
      | mem T hT =>
        obtain ⟨x, rfl⟩ := hT
        rw [u.2.2, hu, map_zero]
      | zero => simp
      | add a b _ _ ha hb => rw [LinearMap.add_apply, map_add (f := _), ha, hb, add_zero]
      | smul c a _ ha => rw [LinearMap.smul_apply, map_smul, ha, smul_zero]
    obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one ℂ hv
    refine Subtype.ext (LinearMap.ext fun w => ?_)
    have h2 := h1 (LinearMap.smulRight l w) (hsp ▸ Submodule.mem_top)
    rw [LinearMap.smulRight_apply, hl, one_smul] at h2
    exact h2
  have hdef : ∀ u, B' u u = 0 → u = 0 := fun u hu => hev u (hdefB _ (u.2.1 v) hu)
  have hinv' : ∀ g u w, B' (eqRep ρ g u) (eqRep ρ g w) = B' u w := fun g u w =>
    hinv g _ _ (u.2.1 _) (w.2.1 _)
  have hmem := UpperTheory.mem_iSup_irreducible_of_admissible_unitary (finU (E := E) (n := n)) (eqForms ρ) (eqRep ρ) B' hdef hinv' (eqRep_adm ρ) ⟨f, hfa, hfe⟩
  refine (iSup_le ?_ : _ ≤ (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1).comap ev) hmem
  rintro ⟨U, hU0, hU, hirr⟩
  let j : U →ₗ[ℂ] S →ₗ[ℂ] (UA E n → ℂ) := (eqForms ρ).subtype ∘ₗ U.subtype
  have hj : ∀ (p : U) (x : infU E n) v, j p (ρ x v) = RU E n x.1 (j p v) := fun p x v => p.1.2.2 x v
  have hrep : IsAutRepU (Pairs.img j) := by
    refine ⟨fun φ hφ => ?_, fun x φ hφ => ?_, fun h => hU0 ?_, fun N hle hN => ?_⟩
    · have h1 : Pairs.img j ≤ autU E n := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        exact p.1.2.1 v)
      exact h1 hφ
    · refine Pairs.stable_of (fun a => ?_) (fun k => ?_) x φ hφ
      · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n a.1) := Submodule.span_le.2 (by
          rintro _ ⟨p, v, rfl⟩
          change RU E n a.1 _ ∈ Pairs.img j
          rw [← hj]
          exact Pairs.apply_mem_img _ _ _)
        exact fun φ hφ => h1 hφ
      · have h1 : Pairs.img j ≤ (Pairs.img j).comap (RU E n k.1) := Submodule.span_le.2 (by
          rintro _ ⟨p, v, rfl⟩
          exact Pairs.apply_mem_img j ⟨eqRep ρ k p.1, hU k _ p.2⟩ v)
        exact fun φ hφ => h1 hφ
    · rw [Submodule.eq_bot_iff]
      intro u hu
      have := Pairs.apply_mem_img j ⟨u, hu⟩ v
      rw [h, Submodule.mem_bot] at this
      exact hev u this
    · refine Pairs.eq_bot_or_eq_img hsp (R := fun x => RU E n x.1) hj
        (Q := fun k : finU (E := E) (n := n) => (eqRep ρ k).restrict (hU k)) (T := fun k => RU E n k.1) (fun _ _ _ => rfl)
        (fun P hP => ?_) hle (fun x => hN x.1) (fun k => hN k.1)
      rcases hirr (P.map U.subtype) (Submodule.map_subtype_le U P) (by
        rintro g _ ⟨p, hp, rfl⟩
        exact ⟨_, hP g p hp, rfl⟩) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_bot _).symm)
      · right
        exact Submodule.map_injective_of_injective U.injective_subtype (h.trans (Submodule.map_subtype_top _).symm)
  intro u hu
  exact le_iSup (fun σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ} => σ.1) ⟨_, hrep⟩
    (Pairs.apply_mem_img j ⟨u, hu⟩ v)
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

theorem UpperTheory.mem_iSup_automorphicReps_of_invariant_form :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (B : (UA E n → ℂ) →ₗ⋆[ℂ] (UA E n → ℂ) →ₗ[ℂ] ℂ), (∀ φ, IsAutFormU φ → B φ φ = 0 → φ = 0) → (∀ x φ ψ, IsAutFormU φ → IsAutFormU ψ → B (RU E n x φ) (RU E n x ψ) = B φ ψ) → ∀ φ : UA E n → ℂ, IsAutFormU φ → φ ∈ ⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1 := by
  intro E _ _ _ n B hdef hinv φ hφ
  classical
  haveI : FiniteDimensional ℂ (admitted.X φ) := hφ.kfin
  have hXA : admitted.X φ ≤ autU E n := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact RU_mem_autU _ _ (mem_autU.2 hφ))
  have haut : ∀ v : admitted.X φ, IsAutFormU (v : UA E n → ℂ) := fun v => mem_autU.1 (hXA v.2)
  let Z : Subrepresentation ((RU E n).comp (infU E n).subtype) :=
    ⟨admitted.X φ, fun g v hv => admitted.RU_mem_X φ g hv⟩
  let ρ : Representation ℂ (infU E n) (admitted.X φ) := Z.toRepresentation
  have hρ : ∀ g (v : admitted.X φ), ((ρ g v : admitted.X φ) : UA E n → ℂ) = RU E n g v := fun _ _ => rfl
  let B' : admitted.X φ →ₗ⋆[ℂ] admitted.X φ →ₗ[ℂ] ℂ := (B.comp (admitted.X φ).subtype).compl₂ (admitted.X φ).subtype
  have hx := UpperTheory.mem_iSup_irreducible_of_admissible_unitary (infU E n) (admitted.X φ) ρ B'
    (fun v hv => Subtype.ext (hdef _ (haut v) hv))
    (fun g u v => hinv g _ _ (haut u) (haut v))
    (fun v => ⟨⊥, fun k hk => by rw [Subgroup.mem_bot.1 hk, map_one]; rfl, inferInstance,
      fun w => Set.finite_range _⟩)
    ⟨φ, admitted.self_mem_X φ⟩
  have hle : (⨆ U : {U : Submodule ℂ (admitted.X φ) // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
      ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) ≤
      (⨆ σ : {σ : Submodule ℂ (UA E n → ℂ) // IsAutRepU σ}, σ.1).comap (admitted.X φ).subtype := by
    refine iSup_le ?_
    rintro ⟨U, h0, hst, hirr⟩ u hu
    let Y : Subrepresentation ρ := ⟨U, fun g v hv => hst g v hv⟩
    let τ : Representation ℂ (infU E n) U := Y.toRepresentation
    have hτ : τ.IsIrreducible := by
      refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨Submodule.nontrivial_iff_ne_bot.2 h0, fun N hN => ?_⟩
      rcases hirr (N.map U.subtype) (Submodule.map_subtype_le _ _) (by
        rintro g _ ⟨w, hw, rfl⟩
        exact ⟨τ g w, hN g w hw, rfl⟩) with h | h
      · left
        exact Submodule.map_injective_of_injective U.injective_subtype (by rw [h, Submodule.map_bot])
      · right
        exact Submodule.map_injective_of_injective U.injective_subtype
          (by rw [h, Submodule.map_top, Submodule.range_subtype])
    exact UpperTheory.admissible_equivariantForms_representation E n B hdef hinv U τ
      (GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ τ hτ)
      ((admitted.X φ).subtype ∘ₗ U.subtype) (fun v => haut v.1) (fun _ _ => rfl) ⟨u, hu⟩
  exact hle hx
