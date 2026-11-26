module

public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.GamAtOfLawsJ
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EveryRowOperatorIsLabelOperatorWithPartner
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzComplexStructureVacuumSolutionEqSmul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystem
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.HSShort.SymCols

variable {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ} (mul : (Fin N → K) →ₗ[K] Module.End K A)

theorem word_const (l : Fin N → K) (n : ℕ) : word mul (fun _ : Fin n => l) = mul l ^ n := by
  simp [word, List.ofFn_const, List.prod_replicate]

theorem join_fun {D : ℕ} (s : Fin D → Fin N → K) (l : Fin N → K) (b : Fin (D + 1)) :
    (fun k => join s l (b, k)) = Fin.lastCases (motive := fun _ => Fin N → K) l s b := by
  induction b using Fin.lastCases with
  | last => funext k; simp [join]
  | cast i => funext k; simp [join]

theorem word_join (hc : ∀ u v, mul u * mul v = mul v * mul u) {D t : ℕ} (s : Fin D → Fin N → K) (l : Fin N → K)
    (β : Fin t → Fin (D + 1)) (α : Fin D →₀ ℕ)
    (hα : ∀ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card = α i) :
    word mul (fun q k => join s l (β q, k)) =
      pw mul s α * mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card := by
  classical
  let P := Submonoid.closure (Set.range mul)
  letI : CommMonoid P := { P.toMonoid with
    mul_comm := by
      intro ⟨x, hx⟩ ⟨y, hy⟩
      apply Subtype.ext
      exact Submonoid.closure_induction₂
        (by rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩; exact hc u v)
        (by simp) (by simp)
        (by
          intro x y z _ _ _ h1 h2
          change x * z = z * x at h1
          change y * z = z * y at h2
          change (x * y) * z = z * (x * y)
          rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc])
        (by
          intro x y z _ _ _ h1 h2
          change z * x = x * z at h1
          change z * y = y * z at h2
          change z * (x * y) = (x * y) * z
          rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]) hx hy }
  let G : (Fin N → K) → P := fun u => ⟨mul u, Submonoid.subset_closure ⟨u, rfl⟩⟩
  let φ : P →* Module.End K A := P.subtype
  have key : ∀ {n : ℕ} (f : Fin n → P), (List.ofFn fun i => φ (f i)).prod = φ (∏ i, f i) := by
    intro n f
    rw [← List.prod_ofFn]
    change (List.ofFn (φ ∘ f)).prod = _
    rw [← List.map_ofFn, map_list_prod]
  let H : Fin (D + 1) → Fin N → K := Fin.lastCases (motive := fun _ => Fin N → K) l s
  have h1 : word mul (fun q k => join s l (β q, k)) = φ (∏ q, G (H (β q))) := by
    rw [← key]
    simp only [word, join_fun]
    rfl
  have h2 : pw mul s α = φ (∏ i, G (s i) ^ α i) := by
    rw [← key]
    simp only [pw, map_pow]
    rfl
  rw [h1, h2, show mul l ^ (Finset.univ.filter fun q => β q = Fin.last D).card = φ (G l ^ (Finset.univ.filter fun q => β q = Fin.last D).card) from (map_pow φ (G l) _).symm, ← map_mul]
  congr 1
  rw [Finset.prod_comp (fun b => G (H b)) β]
  rw [Finset.prod_subset (Finset.subset_univ _)]
  · rw [Fin.prod_univ_castSucc]
    apply congrArg₂ (fun (x y : P) => x * y)
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [H, hα]
    · simp [H]
  · intro b _ hb
    have : (Finset.univ.filter fun q => β q = b).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q _ hq
      exact hb (Finset.mem_image.2 ⟨q, Finset.mem_univ _, hq⟩)
    rw [this]
    exact pow_zero _

theorem card_fibers {D t : ℕ} (β : Fin t → Fin (D + 1)) :
    ∑ i : Fin D, (Finset.univ.filter fun q => β q = i.castSucc).card +
      (Finset.univ.filter fun q => β q = Fin.last D).card = t := by
  classical
  have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := β)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  rw [Fin.sum_univ_castSucc] at this
  exact this.symm

end GlobalTheory.HSShort.SymCols

open GlobalTheory.HSShort.SymCols in
theorem GlobalTheory.HSShort.symbols_of_columns : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → ∀ l : Fin S.N → E, (∀ (a : Fin (S.T - S.D)) (α : MonoDeg (Fin S.D) a) (p : Fin δ), ∃ h : word Φ.mul (fun q k => join s l ((col (ix (⟨a, α⟩, p))).β q, k)) (Φ.ι (col (ix (⟨a, α⟩, p))).x) ∈ Φ.U a, ∀ α' p', Φ.sym a ⟨_, h⟩ (α', p') = if α'.1 = α.1 then (∑ k, l k * Φ.y p' k) ^ (S.T - a) * Φ.res (Φ.ι (m p)) p' else 0) ∧ ∀ k, k ∉ Set.range ix → (col k).j = S.D → word Φ.mul (fun q j => join s l ((col k).β q, j)) (Φ.ι (col k).x) ∈ Φ.U (S.T - S.D) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d col m ix hsh l
  refine ⟨fun a α p => ?_, fun k hk hj => ?_⟩
  · set κ := col (ix (⟨a, α⟩, p)) with hκ
    have hj : κ.j = 0 := hsh.x_j _
    have hx : (κ.x : A) = m p := hsh.x_vec _
    have htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => κ.β q = i.castSucc).card = α.1 i := hsh.x_type _
    have ht : κ.t = S.T := by have := κ.add; omega
    have hdeg : ∑ i : Fin S.D, α.1 i = a := by rw [← Finsupp.degree_eq_sum]; exact α.2
    have hlast : (Finset.univ.filter fun q => κ.β q = Fin.last S.D).card = S.T - a := by
      have := card_fibers κ.β
      simp only [htype, hdeg] at this
      omega
    have heq : word Φ.mul (fun q k => join s l (κ.β q, k)) (Φ.ι κ.x) =
        pw Φ.mul s α.1 (word Φ.mul (fun _ : Fin (S.T - a) => l) (Φ.ι (m p))) := by
      rw [word_join Φ.mul Φ.comm s l κ.β α.1 htype, hlast, word_const, Module.End.mul_apply, hx]
    obtain ⟨h, hsym⟩ := Φ.mono a (by omega) α (fun _ => l) (Φ.ι (m p))
      (Submodule.subset_span ⟨(m p : A), (m p).2, rfl⟩)
    rw [heq]
    refine ⟨h, fun α' p' => ?_⟩
    rw [hsym]
    simp
  · have hrest := hsh.rest k hk
    have hno : ∀ q, (col k).β q ≠ Fin.last S.D := by
      rcases hrest with h | h
      · exact h.2
      · have := hS.le_T; omega
    classical
    let α : Fin S.D →₀ ℕ := Finsupp.equivFunOnFinite.symm
      (fun i => (Finset.univ.filter fun q => (col k).β q = i.castSucc).card)
    have htype : ∀ i : Fin S.D, (Finset.univ.filter fun q => (col k).β q = i.castSucc).card = α i := fun i => rfl
    have h0 : (Finset.univ.filter fun q => (col k).β q = Fin.last S.D).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun q _ => hno q
    have ht : (col k).t = S.T - S.D := by have := (col k).add; omega
    have hdeg : α.degree = S.T - S.D := by
      rw [Finsupp.degree_eq_sum]
      have := card_fibers (col k).β
      rw [h0] at this
      simpa [α, ht] using this
    rw [word_join Φ.mul Φ.comm s l (col k).β α htype, h0, pow_zero, mul_one, Φ.div]
    refine Submodule.mem_iSup_of_mem ⟨α, hdeg⟩ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨((col k).x : A), ?_, rfl⟩))
    have key : ∀ (j : ℕ) (x : S.V j), j = S.D → (x : A) ∈ S.V S.D := by rintro j x rfl; exact x.2
    exact key _ _ hj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymbolsOfEvaluatedColumnsHermitianMultSystemStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symbols_of_evaluated_columns_hermitianMultSystem : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (col : Fin d → S.Col) (m : Fin δ → S.V 0) (ix : (Σ a : Fin (S.T - S.D), MonoDeg (Fin S.D) a) × Fin δ ↪ Fin d), S.Shape δ col m ix → ∀ l : Fin S.N → E, (∀ (a : Fin (S.T - S.D)) (α : MonoDeg (Fin S.D) a) (p : Fin δ), ∃ h : word Φ.mul (fun q k => join s l ((col (ix (⟨a, α⟩, p))).β q, k)) (Φ.ι (col (ix (⟨a, α⟩, p))).x) ∈ Φ.U a, ∀ α' p', Φ.sym a ⟨_, h⟩ (α', p') = if α'.1 = α.1 then (∑ k, l k * Φ.y p' k) ^ (S.T - a) * Φ.res (Φ.ι (m p)) p' else 0) ∧ ∀ k, k ∉ Set.range ix → (col k).j = S.D → word Φ.mul (fun q j => join s l ((col k).β q, j)) (Φ.ι (col k).x) ∈ Φ.U (S.T - S.D) := by
  first | exact @GlobalTheory.HSShort.symbols_of_columns | exact GlobalTheory.HSShort.symbols_of_columns | (intros; apply GlobalTheory.HSShort.symbols_of_columns <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionCuspidalParabolicProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionCuspidalParabolicProduct
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.HCInduction

open Formalism.L2.DIV GlobalTheory.BI

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

theorem parab_eq_blockTri (b : Fin r → Fin s) :
    parab K b = blockTri (κ := K) (fun i => (b i : ℕ)) := by
  ext g
  constructor
  · intro hg
    exact hg.1
  · intro hg
    exact ⟨hg, (blockTri (κ := K) (fun i => (b i : ℕ))).inv_mem hg⟩


omit [Fintype K] [DecidableEq K] in
def blockGL (b : Fin r → Fin s) (c : Fin s) :
    GL (Fin (Fintype.card {i // b i = c})) K ≃* GL {i // b i = c} K :=
  glEquiv K (Fintype.equivFin {i // b i = c}).symm

omit [Fintype K] [DecidableEq K] in
theorem blockGL_apply (b : Fin r → Fin s) (c : Fin s) (g : GL (Fin (Fintype.card {i // b i = c})) K)
    (x y : {i // b i = c}) :
    ((blockGL b c g : GL {i // b i = c} K) : Matrix _ _ K) x y =
      (g : Matrix _ _ K) (Fintype.equivFin _ x) (Fintype.equivFin _ y) := rfl

theorem sum_unipRadical_eq_zero (b : Fin r → Fin s) (c : Fin s) (τ : FDRep ℂ (GL {i // b i = c} K))
    (hτ : IsCuspidal K τ) (c' : Fin (Fintype.card {i // b i = c}) → ℕ) (hc' : ∃ i j, c' i ≠ c' j) :
    ∑ᶠ u : GlobalTheory.FiniteGL.unipRadical K c', LinearMap.trace ℂ τ (τ.ρ (blockGL b c u)) = 0 := by
  classical
  let _ : Fintype (GlobalTheory.FiniteGL.unipRadical K c') := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  let ρu : Representation ℂ (GlobalTheory.FiniteGL.unipRadical K c') τ :=
    τ.ρ.comp ((blockGL b c).toMonoidHom.comp (GlobalTheory.FiniteGL.unipRadical K c').subtype)
  refine (GlobalTheory.GoodTypeGeneric.sum_character_eq_zero_iff ρu).2 ?_
  intro v hv
  obtain ⟨i0, j0, h0⟩ : ∃ i0 j0, c' i0 < c' j0 := by
    obtain ⟨i, j, hij⟩ := hc'
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, j, h⟩
    · exact ⟨j, i, h⟩
  let F := Fintype.equivFin {i // b i = c}
  let bb : {i // b i = c} → Fin 2 := fun x => if c' (F x) ≤ c' i0 then 0 else 1
  have hbb : Function.Surjective bb := by
    intro k
    fin_cases k
    · exact ⟨F.symm i0, by simp [bb]⟩
    · exact ⟨F.symm j0, by simp [bb, not_le.2 h0]⟩
  refine hτ 2 bb hbb le_rfl v fun u hu => ?_
  set u' := (blockGL b c).symm u with hu'def
  have hu'u : blockGL b c u' = u := MulEquiv.apply_symm_apply _ _
  have hent : ∀ k l, (u' : Matrix _ _ K) k l = (u : Matrix _ _ K) (F.symm k) (F.symm l) := by
    intro k l
    rw [← hu'u, blockGL_apply]
    simp [F]
  have hmem : u' ∈ GlobalTheory.FiniteGL.unipRadical K c' := by
    rw [GlobalTheory.FiniteGL.mem_unipRadical]
    intro k l hlk
    rw [Matrix.sub_apply, hent]
    have hb : ∀ m, bb (F.symm m) = if c' m ≤ c' i0 then 0 else 1 := fun m => by simp [bb]
    by_cases hkl : bb (F.symm k) = bb (F.symm l)
    · rw [hu.2 _ _ hkl]
      by_cases e : k = l
      · subst e; simp
      · rw [if_neg (fun h => e (F.symm.injective h)), Matrix.one_apply_ne e, sub_zero]
    · have hk : ¬ c' k ≤ c' i0 := fun hk => hkl (by rw [hb, hb, if_pos hk, if_pos (hlk.trans hk)])
      have hl : c' l ≤ c' i0 := by
        by_contra hl
        exact hkl (by rw [hb, hb, if_neg hk, if_neg hl])
      have hlt : bb (F.symm l) < bb (F.symm k) := by
        rw [hb, hb, if_neg hk, if_pos hl]; decide
      have ekl : k ≠ l := fun e => hkl (by rw [e])
      rw [hu.1.1 _ _ hlt, Matrix.one_apply_ne ekl, sub_zero]
  have := hv ⟨u', hmem⟩
  simpa [ρu, hu'u] using this

theorem isIrrChar_block (b : Fin r → Fin s) (c : Fin s) (τ : FDRep ℂ (GL {i // b i = c} K)) (hτ : Simple τ) :
    IsIrrChar ℂ ℂ (fun g : GL (Fin (Fintype.card {i // b i = c})) K => LinearMap.trace ℂ τ (τ.ρ (blockGL b c g))) := by
  have hi := GlobalTheory.FinGL.Transport.isIrreducible_comp τ.ρ (blockGL b c).toMonoidHom (blockGL b c).surjective
    (GlobalTheory.SerOSys.ZSum.isIrreducible_of_simple τ hτ)
  have h := (isChar_and_isIrrChar_of_rep ℂ ℂ _ τ (τ.ρ.comp (blockGL b c).toMonoidHom)).2 hi
  simpa [Representation.character] using h

theorem isCuspProdChar_trace_hcRep : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b →
    (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → Monotone b →
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x)) := by
  intro K _ _ _ r s b lam _ hlam hmono
  classical
  let b₀ : Fin r → ℕ := fun i => (b i : ℕ)
  have hb₀ : Monotone b₀ := fun i j h => hmono h
  let d : Fin s → ℕ := fun c => Fintype.card {i // b i = c}
  let e : (Σ c, Fin (d c)) ≃ Fin r :=
    (Equiv.sigmaCongrRight fun c => (Fintype.equivFin {i // b i = c}).symm).trans (Equiv.sigmaFiberEquiv b)
  have hbe : ∀ x, b (e x) = x.1 := fun x => ((Fintype.equivFin {i // b i = x.1}).symm x.2).2
  have he : ∀ x y, b₀ (e x) = b₀ (e y) ↔ x.1 = y.1 := by
    intro x y
    simp only [b₀, hbe, Fin.val_inj]
  let χ : ∀ c, GL (Fin (d c)) K → ℂ := fun c g => LinearMap.trace ℂ (lam c) ((lam c).ρ (blockGL b c g))
  obtain ⟨n, σ, hσ, hch⟩ := GlobalTheory.GoodTypeGeneric.exists_isCuspDatum (F := K) hb₀ e he χ
    (fun c => isIrrChar_block b c (lam c) (hlam c).1)
    (fun c c' hc' => sum_unipRadical_eq_zero b c (lam c) (hlam c).2 c' hc')
  refine ⟨n, b₀, σ, hσ, fun x => ?_⟩
  have hPB := parab_eq_blockTri (K := K) b
  let f : blockTri (κ := K) b₀ →* parab K b :=
    MonoidHom.codRestrict (blockTri (κ := K) b₀).subtype (parab K b) (fun p => by rw [hPB]; exact p.2)
  have hf : Function.Surjective f := fun p => ⟨⟨p.1, by rw [← hPB]; exact p.2⟩, rfl⟩
  have h1 : LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) =
      (Representation.coind (parab K b).subtype (PI.SerBridgeGLW.inflRep K b lam)).character x := rfl
  show LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x) = _
  have h2 := GlobalTheory.FinGL.Transport.character_coind (parab K b).subtype (blockTri (κ := K) b₀).subtype
    (PI.SerBridgeGLW.inflRep K b lam) (MulEquiv.refl _) f hf (fun _ => rfl) x
  rw [MulEquiv.refl_apply] at h2
  rw [h1, ← h2]
  rw [GlobalTheory.GoodTypeGeneric.character_coind_eq_ind, GlobalTheory.GoodTypeGeneric.character_coind_eq_ind]
  congr 1
  funext p
  rw [hch p]
  show LinearMap.trace ℂ _ (PiTensorProduct.map fun c => (lam c).ρ (levi K b c (f p))) = _
  rw [PI.SerBridgeGLW.trace_piTensorMap]
  refine Finset.prod_congr rfl fun c _ => ?_
  show _ = LinearMap.trace ℂ (lam c) ((lam c).ρ (blockGL b c _))
  congr 3
  apply Units.ext
  ext x y
  rw [blockGL_apply, GlobalTheory.GoodTypeGeneric.blocksHom_apply]
  have hx : ∀ z : {i // b i = c}, e ⟨c, Fintype.equivFin _ z⟩ = z.1 := fun z => by
    simp [e, Equiv.sigmaFiberEquiv]
  rw [hx, hx]
  rfl

end GlobalTheory.HCInduction
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionCuspidalParabolicProductStatement
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInduction_cuspidalParabolicProduct : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), Function.Surjective b → (∀ c, Simple (lam c) ∧ IsCuspidal K (lam c)) → Monotone b → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar (fun x : GL (Fin r) K => LinearMap.trace ℂ (hcSpace K b lam) (hcRep K b lam x)) := by
  first | exact @GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep | exact GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep | (intros; apply GlobalTheory.HCInduction.isCuspProdChar_trace_hcRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgLatOfOfLowerBound
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory.IntCuspLat

theorem exists_dataX (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (k : (T.U j σ).Comp) :
    ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (T.U j σ).X k ∧ Xx.g = T.Q.l.M ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} ∧ Xx.k0 = 2 * xiR D := by
  obtain ⟨-, -, -, hx0, hx1, -⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have habs := h.xiAbs j hj σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ)) k
  have hξ := GlobalTheory.eq_or_eq_neg_of_purelyImaginary_of_norm_eq _ D.host.xi0 ((T.U j σ).X k).ξ0 D.host.φ₀
    (GlobalTheory.LatticeData.flagDomainConj_hostXi_eq_neg D) ((T.U j σ).X k).ξ0_im (habs _).symm
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((T.U j σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rcases hξ with e | e
    · rw [e]; exact h1
    · rw [e, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
        ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
      exact h1
  have hM : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  obtain ⟨Xx, h1, h2, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((T.U j σ).X k) D.host.AA D.host.AAbar
    (xiR D) T.Q.l.M
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (fun γ => gamAt_of_lawsM D T h j hj σ hσ k γ)
  exact ⟨{ Xx with
    k0 := 2 * xiR D
    minWeight_pos := by positivity
    k0_le := by linarith
    ξ0_abs := fun τ => by rw [show Xx.ξ0 = ((T.U j σ).X k).ξ0 from congrArg _ h1, habs]; ring }, h1, h2, h3, rfl⟩

theorem exists_lowerBound (D : D7) (T : Core D) (h : LawsM T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) :
    ∃ B : ℝ, ∀ F ∈ T.C j w, (∀ la, ∀ v ∈ T.Vs j la, 0 ≤ v F) → F ≠ 0 →
      -B ≤ ∑ σ : T.Q.c.F →+* ℂ, Real.log (T.Ns j w σ F) := by
  classical
  obtain ⟨C0, hC0, hroom⟩ := GlobalTheory.room_of_constants
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := (h.unf j hj T.σ₀ T.good_σ₀).1.symm
  have hf := GlobalTheory.WtSizes.fdeg_eq D
  have hd1 := GlobalTheory.WtSizes.one_le_dE D
  have hts := GlobalTheory.WtSizes.tot_le_size w
  have hwf : ∀ k, (∑ τ, ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ) ≤ w.size := fun k => by
    refine (Finset.sum_le_sum fun τ _ => GlobalTheory.WtSizes.spread_laU_le T hr w k τ).trans (le_trans ?_ hts)
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · exact_mod_cast GlobalTheory.WtSizes.sum_cm_le ((T.U j T.σ₀).X k) (GlobalTheory.WtSizes.tot w)
    · rw [Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (T.U j T.σ₀).X k), hf, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_mul_of_pos_right _ hr
  have hsz : ((∑ b : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult b), wtA w (b, i) : ℕ) : ℝ) +
      ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
    refine le_trans (add_le_add ?_ le_rfl) hts
    exact_mod_cast Finset.sum_le_sum fun b _ => GlobalTheory.WtSizes.sum_wtA_le_tot w b _
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  haveI : NeZero D.host.d := ⟨D.host.hyp.2.1.ne_zero⟩
  have hd4 : D.host.d % 4 = 3 := by
    have := T.Q.H.d_mod
    rw [h.pins.1.1] at this
    omega
  obtain ⟨_, χ, hχ, -⟩ := GlobalTheory.LamF.exists_kronecker_logOm_re D.host.E h.pins.1.1 hd4
  have g0 := (D.host.g_prime 0).pos
  have g1 := (D.host.g_prime 1).pos
  have hdpos : 0 < D.host.d := lt_of_le_of_lt (Nat.zero_le _) D.host.qd_big.2
  have hN : 0 < Ideal.absNorm D.host.ccK :=
    Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ((D.host.g 0 * D.host.g 1 * (Ideal.absNorm D.host.ccK * D.host.d) : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hM : (0 : ℝ) < M := by
    rw [hMdef]
    exact_mod_cast Nat.mul_pos (Nat.mul_pos g0 g1) (Nat.mul_pos hN hdpos)
  refine ⟨(C0 * ((fdeg D.host.E : ℝ) * D.R.r + |Real.log (M * (2 * xiR D))| + Real.log (dE D.host.E) +
    |(GlobalTheory.CM.logOm D.host.E χ).re|) ^ (2 : ℝ) * (1 + Real.log w.size) * w.size) *
      (Module.finrank ℚ T.Q.c.F : ℝ), fun F hFC hF hF1 => ?_⟩
  have hhol : rdU (T.U j T.σ₀) F ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) :=
    ((mem_cusp _ _ _ _ _ F).1 hFC).2 T.σ₀ T.good_σ₀
  have hSS := Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) hhol
  have hfin : supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F) ≠ ⊤ :=
    supE_cusp_ne_top T.good_σ₀ hFC
  have hpos : 0 < supN (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) (rdU (T.U j T.σ₀) F) := by
    rcases (ENNReal.toReal_nonneg : 0 ≤ (supE (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
      (rdU (T.U j T.σ₀) F)).toReal).lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (h.supDef j hj (wtA w) w.n (dom_wtA w) T.σ₀ T.good_σ₀ F hFC heq.symm) hF1
  obtain ⟨k, z0, hz0, hlt⟩ := Formalism.L2.Pj.abelian₂.half_max (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)
    (rdU (T.U j T.σ₀) F) hpos hfin
  have hhalf : ∀ x ∈ ((T.U j T.σ₀).X k).dom, ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k)
      (rdU (T.U j T.σ₀) F k) x ≤
      2 * ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) z0 :=
    fun x hx => (Formalism.L2.Pj.abelian₂.pnorm_le_supN _ _ _ hfin k x hx).trans hlt.le
  have hposz : 0 < ((T.U j T.σ₀).X k).pnorm (laU (T.U j T.σ₀) (wtA w) w.n k) (rdU (T.U j T.σ₀) F k) z0 := by
    linarith
  obtain ⟨Xx, hX, hXg, hΛ, hk0⟩ := exists_dataX D T h j hj T.σ₀ T.good_σ₀ k
  have habs : ∀ τ : D.host.E →+* ℂ,
      ‖τ Xx.ξ0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := fun τ => by
    rw [← GlobalTheory.TransvModel.xiR_eq, ← h.xiAbs j hj T.σ₀ T.good_σ₀ k τ, ← hX]
  have htr : ∀ v ∈ Xx.L', FD.herm ((T.U j T.σ₀).X k).Gm v v = 0 → ∀ b : D.host.E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ ((T.U j T.σ₀).X k).Γ, ∀ τ : ((T.U j T.σ₀).X k).Ψ,
        (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ.1 = ((T.U j T.σ₀).X k).flowMat v τ ((M : ℂ) * τ.1 b) := by
    rw [← hX]
    intro v hv hiso b hb hbi
    have := GlobalTheory.TransvModel.transv_mem_of_span Xx (D.host.AA : Set D.host.E) hΛ (Ideal.absNorm D.host.ccK * D.host.d)
      (GlobalTheory.TransvModel.isIntegral_level_mul_kappa Xx.toData hN hdpos D.host.φ₀ (habs _)) v hv hiso b hb hbi
    rwa [hXg.trans h.pins.2.1.1, ← hMdef] at this
  obtain ⟨x, lam, hx, hLB, hPx⟩ := Formalism.L2.Pj.abelian₂.cm_frame_of_eq Xx ((T.U j T.σ₀).X k) hX _ _ z0 M w.size (hSS k) hM
    (hwf k) w.one_le_size hr (fun v hv hvv b hb hbi => by
      obtain ⟨γ, hγ, hγ'⟩ := htr v hv hvv b hb hbi
      exact ⟨γ, hγ, h.chiTriv j hj T.σ₀ T.good_σ₀ _ _ (dom_wtA w) k γ hγ, hγ'⟩) hz0 hhalf hposz
  have hf1 : 1 ≤ fdeg D.host.E := by
    have h2 := finrank_eq_two_mul_half_degree (E := D.host.E)
    have h3 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have h4 : Module.finrank ℚ D.host.E = 2 * fdeg D.host.E := by exact_mod_cast h2
    omega
  have hlog : Real.log (M * Xx.k0) ≤ 19 * |Real.log (M * (2 * xiR D))| + 3 + Real.log (dE D.host.E) := by
    rw [hk0]
    have := le_abs_self (Real.log (M * (2 * xiR D)))
    have := abs_nonneg (Real.log (M * (2 * xiR D)))
    have := Real.log_nonneg hd1
    linarith
  obtain ⟨hLa1, hr'⟩ := hroom (fdeg D.host.E) D.R.r Xx.p0 (dE D.host.E) _ (GlobalTheory.CM.logOm D.host.E χ).re M Xx.k0 w.size
    hf1 hr Xx.p0_le hd1 (abs_nonneg _) hM Xx.minWeight_pos w.one_le_size hlog
  have hr'' := hr' _ _ (Nat.cast_nonneg _) (by positivity) hsz C0 2 le_rfl le_rfl
  have hNs : ∀ σ, IsNormOn (T.C j w) σ (T.Ns j w σ) := fun σ =>
    (isNormOn_supC _ (h.supDef j hj) (dom_wtA w) (goodEmb_goodOf _ σ)).of_goodOf
  have hSpos : ∀ σ, 0 < supC (T.Q.Xo j) T.Q.c (T.U j) (xiR D) (goodOf T.Q.c σ) (wtA w) w.n F := fun σ =>
    lt_of_le_of_ne ((hNs σ).nonneg F hFC) fun h0 => hF1 ((hNs σ).defin F hFC h0.symm)
  have h5 := GlobalTheory.LamT.meanLogSup_lowerBound D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (xiR D)
    (h.unf j hj) (h.xiAbs j hj) (by rw [hpq]; exact hr) χ hχ (wtA w) w.n (dom_wtA w) F hFC hF hSpos k ⟨x, hx⟩ Xx hX
    D.host.AA (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) hΛ _ lam hLa1 hLB hPx
  have hf' : Module.finrank ℚ D.host.E / 2 = D.R.f := hf
  rw [hf'] at h5
  have hK : (0 : ℝ) < Module.finrank ℚ T.Q.c.F := by exact_mod_cast Module.finrank_pos
  rw [← neg_mul, ← le_div_iff₀ hK]
  refine le_trans ?_ h5
  linarith

theorem fg_latOf_of_lowerBound {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] (C : Submodule K R) [FiniteDimensional K C]
    (Vs : HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (N : (K →+* ℂ) → R → ℝ) (hN : ∀ σ, IsNormOn C σ (N σ)) (B : ℝ)
    (hB : ∀ F ∈ C, (∀ la, ∀ v ∈ Vs la, 0 ≤ v F) → F ≠ 0 → -B ≤ ∑ σ : K →+* ℂ, Real.log (N σ F)) :
    (latOf C Vs hV).FG := by
  let Nf : TB.NormFam K C :=
    { N := fun σ F => N σ F
      nonneg := fun σ F => (hN σ).nonneg _ F.2
      eq_zero := fun σ F h0 => Subtype.ext ((hN σ).defin _ F.2 h0)
      smul := fun σ a F => (hN σ).smul a _ F.2
      add := fun σ F G => (hN σ).add _ F.2 _ G.2 }
  exact formalGroup_of_discriminant _ _ Nf _ (discriminant_of_product_lower _ _ Nf _ B fun F hF h0 =>
    hB F.1 F.2 hF fun h1 => h0 (Subtype.ext h1))

end GlobalTheory.IntCuspLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.CarriedHecke

theorem exists_sys_of_mem_span {K V H I J : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup H] [Module ℂ H]
    (σ : K →+* ℂ) (op : I → Module.End K V) (j : V →ₛₗ[σ] H) (h : J → Module.End ℂ H) (ι : J → I)
    (hj : ∀ i f, j (op (ι i) f) = h i (j f)) (hc : Formalism.L2.Col.PairComm h) (C : (I → K) → Prop) (v : H)
    (hv : v ∈ Submodule.span ℂ (j '' (Formalism.L2.Col.eigSum op C : Set V))) (hv0 : v ≠ 0) (l : J → ℂ)
    (he : ∀ i, h i v = l i • v) : ∃ x, C x ∧ ∀ i, σ (x (ι i)) = l i := by
  classical

  have hstep : ∀ (i : J) (a : K) (k : ℕ) (g : V),
      ((h i - σ a • 1) ^ k) (j g) = j (((op (ι i) - a • 1) ^ k) g) := by
    intro i a k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih]
      simp [hj, map_smulₛₗ]
  have himg : ∀ x, ∀ f ∈ Formalism.L2.Col.eigAt op x, j f ∈ Formalism.L2.Col.eigAt h (fun i => σ (x (ι i))) := by
    intro x f hf
    rw [Formalism.L2.Col.eigAt, Submodule.mem_iInf] at hf ⊢
    intro i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 (hf (ι i))
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, by rw [hstep, hk, map_zero]⟩
  set T : Submodule ℂ H := ⨆ (x : I → K) (_ : C x), Formalism.L2.Col.eigAt h (fun i => σ (x (ι i))) with hT
  have hle : Formalism.L2.Col.eigSum op C ≤ T.comap j := by
    refine iSup₂_le fun x hx f hf => ?_
    exact (le_iSup₂_of_le (f := fun (x : I → K) (_ : C x) => Formalism.L2.Col.eigAt h (fun i => σ (x (ι i)))) x hx le_rfl)
      (himg x f hf)
  have hvT : v ∈ T := by
    refine (Submodule.span_le.2 ?_) hv
    rintro _ ⟨f, hf, rfl⟩
    exact hle hf
  have hvl : v ∈ Formalism.L2.Col.eigAt h l := Formalism.L2.Col.mem_eigAt_of_forall_apply he
  by_contra hno
  push_neg at hno
  have hT' : T ≤ ⨆ (y : J → ℂ) (_ : y ≠ l), Formalism.L2.Col.eigAt h y := by
    refine iSup₂_le fun x hx => ?_
    obtain ⟨i, hi⟩ := hno x hx
    exact le_iSup₂_of_le (f := fun (y : J → ℂ) (_ : y ≠ l) => Formalism.L2.Col.eigAt h y) (fun i => σ (x (ι i)))
      (fun e => hi (congrFun e i)) le_rfl
  exact hv0 ((Submodule.disjoint_def.1 (Formalism.L2.Col.iSupIndep_eigAt hc l)) v hvl (hT' hvT))

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]


set_option maxHeartbeats 1000000 in
theorem hecke_polys_of_carries : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ p c, R.Carries p c → ∀ P ∈ A3.A.ok A3.A.μ0, RealDat.polE (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) ∧ RealDat.polW (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (splitLab D.R.r k)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hI hok hW hEx hS hinj p c hcar P hP
  obtain ⟨hC, hSF, hEE, -⟩ := GlobalTheory.T.core_clauses_of_weak_characterisation R F hW hEx
  obtain ⟨hG, hcj, hq⟩ := (GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev).2.2.2 hC.fam A3.A.μ0 P hP
  have hq0 : (A3.A.q P : ℂ) ≠ 0 := by
    rw [hq, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact (R.pl P).ne_bot
  obtain ⟨_, _, _, htie⟩ := hC.fam.tie
  obtain ⟨-, hr, ht⟩ := htie.ranks
  have hrX : D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t := by rw [D.sp.X'_rank, hr, ht]; rfl
  have hrY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]; simp [Ranks.rankY]
  have hr0 : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hm0 : 0 < D.R.m := by have := D.R.two_le_m; omega

  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcar.1
  have hwp : w ∈ R.EEp3 p :=
    (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.EEc c) c hcar) hw
  have hv0 : LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := fun h0 => hw0 (hinj p w hwp h0)
  have hwE : w ∈ EEc R.toRealDat R.SF c := (hEE c) ▸ hw
  obtain ⟨hX, hXo, hXn⟩ := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0
  obtain ⟨zE, hmE, hpE⟩ := GlobalTheory.T.exists_splitPrime_heckeTransfer_compositeLift R.toRealDat F.lv2 hI hC hS A3.A.μ0 ⟨P, hP⟩
  have heig : ∀ k : Fin (D.sp.X'.rank + 1), hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)
      (LinearMap.adjoint (R.Th A3.A.μ0) w) = GlobalTheory.Hk3.evC (Yc D 0) (R.pl P) (fun d => c (R.pl P) (dualLab d))
        (GlobalTheory.Hk3.splitC (Yc D 0).rank (zE k)) • LinearMap.adjoint (R.Th A3.A.μ0) w := fun k =>
    (GlobalTheory.T.matched_spherical_pairs_commute_composite_lift R.toRealDat F.lv2 hC hS R.SF hSF A3.A.μ0 (R.pl P) hG _ _ (hmE k (Nat.lt_succ_iff.1 k.2)) hX hXo).2 c w hwE
  obtain ⟨x, hx, hxe⟩ := exists_sys_of_mem_span D.what₂.embLL (A3.rowI A3.A.μ0).opAll (R.jX A3.A.μ0)
    (fun k : Fin (D.sp.X'.rank + 1) => hX (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1))
    (fun k => Sum.inl ((⟨P, hP⟩ : A3.A.ok A3.A.μ0), (k : ℕ)))
    (fun k f => (GlobalTheory.T.familySplitOperators_eq_labelOperators_models R.toRealDat F.lv2 hC.lev hC.fam hC.models).1 A3.A.μ0 hX hXo ⟨P, hP⟩ k
      (Nat.lt_succ_iff.1 k.2) f)
    (fun k k' => hXn.1 _ _ hG hG _ _) _ _ (hcar.2 (Submodule.mem_map_of_mem hw)) hv0 _ heig

  have hE : (p.1.1 P).map D.what₂.embLL =
      (Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) fun j => c (R.pl P) (dualLab (splitLab D.R.r j))).comp
        (C ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) * X) := by
    have h1 := hpE fun j => c (R.pl P) (dualLab (splitLab (Yc D 0).rank j))
    have h2 : (Formalism.L2.Col.heckePolyOf (A3.A.r + D.R.m * A3.A.t) (A3.A.q P) fun k => x (Sum.inl (⟨P, hP⟩, k))) =
        p.1.1 P * (A3.A.fam.R A3.A.μ0).blockProd ⟨P, hP⟩ := hx.1 ⟨P, hP⟩
    have h3 := congrArg (Polynomial.map D.what₂.embLL) h2
    rw [Formalism.L2.Col.map_heckePolyOf, Polynomial.map_mul, ← hrX] at h3
    rw [GlobalTheory.Hk3.Link.heckePolyOf_congr _ _ (b := fun k => D.what₂.embLL (x (Sum.inl (⟨P, hP⟩, k)))) ?_, h3, hrY] at h1
    · refine mul_right_cancel₀ ?_ h1
      rw [Ne, Polynomial.map_eq_zero]
      unfold BlockDat.blockProd
      refine List.prod_ne_zero fun h => ?_
      obtain ⟨ν, -, hν⟩ := List.mem_map.1 h
      exact GlobalTheory.Hk3.Link.blockPoly_ne_zero _ _ _ hν
    · intro k hk
      have h5 := hxe ⟨k, Nat.lt_succ_iff.2 hk⟩
      exact (h5.trans (GlobalTheory.Hk3.Link.evC_splitC (Yc D 0) (R.pl P) hcj _ _)).symm

  obtain ⟨h, hEo, -, -, hev, -⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hC hS R.SF hSF
  have hne : R.HE.e w ≠ 0 := fun h0 => hw0 ((hC.models.HE).1 (h0.trans (map_zero _).symm))
  obtain ⟨v, hv⟩ : ∃ v, R.HE.e w v ≠ 0 := by
    by_contra hcon
    exact hne (MultilinearMap.ext fun v => not_not.1 fun hv => hcon ⟨v, hv⟩)
  obtain ⟨cc, hβ⟩ := hC.lev.βY 0 hm0
  have hlev := (GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ (R.pl P)
    (by
      have hN := ((GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev).2.1 A3.A.μ0 (R.pl P) hG).1
      rw [Nat.cast_pow]
      intro hmem
      rcases Nat.eq_zero_or_pos cc with h0 | h0
      · rw [h0, pow_zero] at hmem
        exact (R.pl P).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hmem)
      · exact hN ((R.pl P).isPrime.mem_of_pow_mem _ hmem))
    (fun PP hPP => hG PP (Or.inl (hPP.resolve_right (Finset.notMem_empty _))))).1
  have hm := (Submodule.mem_inf.1 (Submodule.mem_comap.1 hwE)).1
  have hrel := GlobalTheory.Hk3.Link.eig_rel (Yc D 0) (R.pl P) hcj _ hv (fun k hk g =>
      (GlobalTheory.Hk3.Link.mult_lev R.θ _ _ _ _ hm v k (hlev k hk).1 g).trans
        ((congrArg (fun z : ℂ => z * R.HE.e w v g) (hlev k hk).2).trans (one_mul _)))
      (fun d => c (R.pl P) (dualLab d)) (fun d hd => by
      have h5 := (hEo (R.pl P) hG (Finsupp.single d 1) w).symm.trans
        ((congrArg R.HE.e (hev c _ hG (Finsupp.single d 1) w hwE)).trans (map_smul _ _ _))
      exact congrArg (fun U : MMap (R.MY 0) => U v) (h5.trans
        (congrArg (fun z : ℂ => z • R.HE.e w) (GlobalTheory.Hk3.Link.evC_single (Yc D 0) (R.pl P) _ d hd))))
  rw [hrY] at hrel
  simp only [dualLab_dualLab] at hrel
  obtain ⟨hb0, hab⟩ := hrel
  have hrr : c (R.pl P) (splitLab D.R.r D.R.r) * c (R.pl P) (dualLab (splitLab D.R.r D.R.r)) = 1 := by
    rw [hab D.R.r le_rfl, Nat.sub_self, hb0]
  have hbr : c (R.pl P) (dualLab (splitLab D.R.r D.R.r)) ≠ 0 := right_ne_zero_of_mul_eq_one hrr
  have ha0 : c (R.pl P) (splitLab D.R.r 0) = 1 := by
    have := hab 0 (Nat.zero_le _)
    rw [Nat.sub_zero] at this
    exact mul_right_cancel₀ hbr (this.trans (one_mul _).symm)
  have hba : ∀ j, j ≤ D.R.r → c (R.pl P) (dualLab (splitLab D.R.r j)) * c (R.pl P) (splitLab D.R.r D.R.r) =
      c (R.pl P) (splitLab D.R.r (D.R.r - j)) := by
    intro j hj
    have := hab (D.R.r - j) (Nat.sub_le _ _)
    rw [Nat.sub_sub_self hj] at this
    rw [← this, mul_assoc, mul_comm _ (c (R.pl P) (splitLab D.R.r D.R.r)), hrr, mul_one]
  have hdual := GlobalTheory.T.dualPoly_twistedHeckePoly_eq_contragredient ℂ D.R.r (A3.A.q P) (fun j => c (R.pl P) (splitLab D.R.r j))
    (fun j => c (R.pl P) (dualLab (splitLab D.R.r j))) ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) 1 hq0
    (pow_ne_zero _ hq0) hr0 ha0 hba
  have hs0 : ((A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t)) ≠ 0 := pow_ne_zero _ hq0
  constructor
  · unfold RealDat.polE
    rw [hE, Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hs0, C_1, one_mul, Polynomial.comp_X]
  · unfold RealDat.polW
    rw [GlobalTheory.Hk3.Link.dualPoly_map, hE, map_pow, map_natCast]
    have hsc : (A3.A.q P : ℂ) ^ (D.R.r - 1 + D.R.m / 2 * D.R.t) =
        (A3.A.q P : ℂ) ^ (D.R.m / 2 * D.R.t) * 1 * (A3.A.q P : ℂ) ^ (D.R.r - 1) := by
      rw [pow_add]; ring
    rw [hsc, hdual, C_1, one_mul, Polynomial.comp_X]

end GlobalTheory.CarriedHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystemStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePolynomials_of_carried_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ p c, R.Carries p c → ∀ P ∈ A3.A.ok A3.A.μ0, RealDat.polE (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) ∧ RealDat.polW (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (splitLab D.R.r k)) := by
  first | exact @GlobalTheory.CarriedHecke.hecke_polys_of_carries | exact GlobalTheory.CarriedHecke.hecke_polys_of_carries | (intros; apply GlobalTheory.CarriedHecke.hecke_polys_of_carries <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemRelationOfGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemRelationOfGenericPoint
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open AlgebraicGeometry TopologicalSpace CategoryTheory GlobalTheory.Points GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory.Adelic.GenericRel

theorem eval₂_mul_of_isHomogeneous {σ R A : Type} [CommSemiring R] [CommSemiring A] (φ : R →+* A)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.IsHomogeneous d) (c : A) (v : σ → A) :
    eval₂ φ (fun i => c * v i) p = c ^ d * eval₂ φ v p := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 ha)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

variable {F : Type} [Field F] (S : LinSys F)

noncomputable def relFn (c : S.L.ι) {r e : ℕ} (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (m : ℕ)
    (a : Fin m → MvPolynomial (Fin r) F) : Γ(S.Y, S.L.U c) :=
  zfun th c ^ m + ∑ k, eval₂ ((resG S.Y le_top).comp (algebraMap F Γ(S.Y, ⊤)))
    (fun i => (S.comb (u i)).f c) (a k) * zfun th c ^ (k : ℕ)

theorem valR_relFn {K : Type} [Field K] (x : Sp K ⟶ S.Y) (c : S.L.ι) (hx : ptOf x ∈ S.L.U c) {r e : ℕ}
    (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F) :
    valR x (S.L.U c) (relFn S c u th m a) = valR x (S.L.U c) (zfun th c) ^ m + ∑ k, eval₂ (S.baseHom x)
      (fun i => valR x (S.L.U c) ((S.comb (u i)).f c)) (a k) * valR x (S.L.U c) (zfun th c) ^ (k : ℕ) := by
  have h := (le_iff_ptOf_mem x _).2 hx
  have hc : (valMap x _ h).hom.comp ((resG S.Y le_top).comp (algebraMap F Γ(S.Y, ⊤))) = S.baseHom x := by
    ext b
    exact ((valR_eq x _ h _).symm.trans (valR_res x le_top h _)).trans (S.valR_algebraMap x b)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [relFn, valR_eq x _ h, map_add (f := _), map_sum, map_mul, map_pow, eval₂_comp_left, hc]
  rfl

theorem relation_of_generic (F : Type) [Field F] (S : LinSys F) (hY : AlgebraicGeometry.IsIntegral S.Y)
    (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (η : S.Y) (hη : IsGenericPoint η Set.univ)
    (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F) (ha : ∀ k, (a k).IsHomogeneous (e * (m - k)))
    (h0 : S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η))
      (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ) = 0)
    (K : Type) [Field K] [Algebra F K] (x : S.Pt K) :
    S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) *
      S.powVal x.1 th ^ (k : ℕ) = 0 := by
  have hxU : ptOf x.1 ∈ S.L.U (S.chartAt (ptOf x.1)) := S.mem_chartAt _
  have hηU : ptOf (resPt η) ∈ S.L.U (S.chartAt (ptOf x.1)) := by
    rw [ptOf_resPt]
    exact (hη.mem_open_set_iff (S.L.U _).isOpen).2 ⟨_, trivial, hxU⟩
  obtain ⟨c0, hc0, hv, hp⟩ := S.exists_frame_change (resPt η) _ hηU
  have hzero : valR (resPt η) _ (relFn S (S.chartAt (ptOf x.1)) u th m a) = 0 := by
    rw [valR_relFn S _ _ hηU, hp (e : ℤ) th]
    simp only [hv, zpow_natCast, eval₂_mul_of_isHomogeneous _ (ha _)]
    calc _ = c0 ^ (e * m) * (S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η))
          (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ)) := by
          rw [mul_add, Finset.mul_sum, mul_pow, ← pow_mul]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_pow, ← pow_mul, show e * m = e * (m - k) + e * k by
            rw [← mul_add, Nat.sub_add_cancel k.2.le], pow_add]
          ring
      _ = 0 := by rw [h0, mul_zero]
  have hb : S.Y.basicOpen (relFn S (S.chartAt (ptOf x.1)) u th m a) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hm : η ∈ S.Y.basicOpen (relFn S (S.chartAt (ptOf x.1)) u th m a) :=
      (hη.mem_open_set_iff (S.Y.basicOpen _).isOpen).2 ⟨y, trivial, hy⟩
    rw [← ptOf_resPt η] at hm
    exact ((valR_ne_zero_iff (resPt η) hηU _).2 hm hzero).elim
  have hf : relFn S (S.chartAt (ptOf x.1)) u th m a = 0 := by
    haveI := hY
    exact (basicOpen_eq_bot_iff _).1 hb
  have key := valR_relFn S x.1 _ hxU u th m a
  rw [hf, valR_zero x.1 _ ((le_iff_ptOf_mem _ _).2 hxU)] at key
  have e2 : ∀ i, valR x.1 _ ((S.comb (u i)).f (S.chartAt (ptOf x.1))) =
      ∑ j, algebraMap F K (u i j) * S.coords x.1 j := fun i =>
    (S.val_comb x.1 (u i)).trans (by rw [LinSys.baseHom_ptOver])
  simp only [e2, LinSys.baseHom_ptOver] at key
  simp only [aeval_def]
  exact key.symm

end GlobalTheory.Adelic.GenericRel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemRelationOfGenericPointStatement
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSystem_relation_of_generic_point : ∀ (F : Type) [Field F] (S : LinSys F), AlgebraicGeometry.IsIntegral S.Y → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (η : S.Y), IsGenericPoint η Set.univ → ∀ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) → S.powVal (resPt η) th ^ m + ∑ k, MvPolynomial.eval₂ (S.baseHom (resPt η)) (fun i => S.val (resPt η) (S.comb (u i))) (a k) * S.powVal (resPt η) th ^ (k : ℕ) = 0 → ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.Adelic.GenericRel.relation_of_generic | exact GlobalTheory.Adelic.GenericRel.relation_of_generic | (intros; apply GlobalTheory.Adelic.GenericRel.relation_of_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentsOfConeIntegralEquation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentsOfConeIntegralEquation
open MvPolynomial

namespace GlobalTheory

theorem coeff_eval₂_C_mul_X {F K : Type} [Field F] [Field K] (φ : F →+* K) {r : ℕ} (w : Fin r → K)
    (p : MvPolynomial (Fin r) F) (d : ℕ) :
    (MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) p).coeff d
      = MvPolynomial.eval₂ φ w (homogeneousComponent d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    have hprod : (u.prod fun i k => (Polynomial.C (w i) * Polynomial.X : Polynomial K) ^ k)
        = Polynomial.C (u.prod fun i k => w i ^ k) * Polynomial.X ^ (Finsupp.degree u) := by
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
        Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
    have hcomp : homogeneousComponent d (monomial u a)
        = if Finsupp.degree u = d then monomial u a else 0 := by
      ext v
      rw [coeff_homogeneousComponent]
      by_cases hd : Finsupp.degree u = d
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
      · by_cases hv : u = v
        · subst hv; simp [hd]
        · simp [coeff_monomial, hv, hd]
    rw [eval₂_monomial, hprod, hcomp, ← mul_assoc, RingHom.comp_apply, ← map_mul,
      Polynomial.coeff_C_mul_X_pow]
    by_cases h : Finsupp.degree u = d
    · subst h
      simp [eval₂_monomial]
    · have h' : d ≠ Finsupp.degree u := fun e => h e.symm
      simp [h, h']
  | add p q hp hq =>
    simp only [eval₂_add, Polynomial.coeff_add, map_add (f := _), hp, hq]

theorem homogeneous_components_of_integral_equation (F K : Type) [Field F] [Field K] (φ : F →+* K)
    (r e m : ℕ) (w : Fin r → K) (τ : K) (b : Fin m → MvPolynomial (Fin r) F)
    (h : (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ)
      (fun i => Polynomial.C (w i) * Polynomial.X) (b k) *
        (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0) :
    ∃ a : Fin m → MvPolynomial (Fin r) F, (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧
      τ ^ m + ∑ k, MvPolynomial.eval₂ φ w (a k) * τ ^ (k : ℕ) = 0 := by
  refine ⟨fun k => homogeneousComponent (e * (m - k)) (b k),
    fun k => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hc := congrArg (fun P : Polynomial K => P.coeff (e * m)) h
  simp only [Polynomial.coeff_add, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hc
  have hpow : ∀ n : ℕ, (Polynomial.C τ * Polynomial.X ^ e) ^ n
      = Polynomial.C (τ ^ n) * Polynomial.X ^ (e * n) := by
    intro n
    rw [mul_pow, ← pow_mul, map_pow]
  have hterm : ∀ k : Fin m, (MvPolynomial.eval₂ (Polynomial.C.comp φ)
      (fun i => Polynomial.C (w i) * Polynomial.X) (b k) *
        (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ)).coeff (e * m)
      = MvPolynomial.eval₂ φ w (homogeneousComponent (e * (m - k)) (b k)) * τ ^ (k : ℕ) := by
    intro k
    have hle : e * (k : ℕ) ≤ e * m := Nat.mul_le_mul_left e k.is_lt.le
    rw [hpow, ← mul_assoc, Polynomial.coeff_mul_X_pow', if_pos hle, Polynomial.coeff_mul_C,
      ← Nat.mul_sub, coeff_eval₂_C_mul_X]
  rw [hpow, Polynomial.coeff_C_mul_X_pow, if_pos rfl] at hc
  simpa only [hterm] using hc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentsOfConeIntegralEquationStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_components_of_cone_integral_equation : ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e m : ℕ) (w : Fin r → K) (τ : K) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 → ∃ a : Fin m → MvPolynomial (Fin r) F, (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ τ ^ m + ∑ k, MvPolynomial.eval₂ φ w (a k) * τ ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.homogeneous_components_of_integral_equation | exact GlobalTheory.homogeneous_components_of_integral_equation | (intros; apply GlobalTheory.homogeneous_components_of_integral_equation <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.SecIntegral

theorem exists_integral_relation : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∃ (m : ℕ) (a : Fin m → MvPolynomial (Fin r) F), (∀ k, (a k).IsHomogeneous (e * (m - k))) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), S.powVal x.1 th ^ m + ∑ k, aeval (fun i => ∑ j, algebraMap F K (u i j) * S.coords x.1 j) (a k) * S.powVal x.1 th ^ (k : ℕ) = 0 := by
  intro F _ S hS r e u th hcov
  have hI : AlgebraicGeometry.IsIntegral S.Y := hS.isIntegral
  have hη : IsGenericPoint (genericPoint S.Y) Set.univ := by
    simpa using genericPoint_spec S.Y
  obtain ⟨m, b, hb⟩ := GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring F (S.Y.residueField (genericPoint S.Y)) (S.baseHom (resPt (genericPoint S.Y))) r e
    (fun i => S.val (resPt (genericPoint S.Y)) (S.comb (u i))) (S.powVal (resPt (genericPoint S.Y)) th)
    (GlobalTheory.T.exists_ratio_mem_valuationSubring_at_generic_point F S hS r e u th hcov _ hη)
  obtain ⟨a, ha, h0⟩ := GlobalTheory.T.homogeneous_components_of_cone_integral_equation _ _ _ r e m _ _ b hb
  exact ⟨m, a, ha, GlobalTheory.T.linearSystem_relation_of_generic_point F S hI r e u th _ hη m a ha h0⟩

end GlobalTheory.SecIntegral
end
end
