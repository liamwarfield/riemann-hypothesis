module

public import Development.WeilBound.ThetaLifts.CartanFactorisation.Factor

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.CartanFactorisation.CommuteConj
section -- merged from Development.WeilBound.ThetaLifts.CartanFactorisation.CountableCompactOpen
noncomputable section

namespace PositivityTheory.ThKF

theorem schur_match {Q Q' P P₂ ι : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup Q'] [Module ℂ Q'] [AddCommGroup P]
    [Module ℂ P] [AddCommGroup P₂] [Module ℂ P₂] [Nontrivial P₂] (S : Submodule ℂ Q) (S' : Submodule ℂ Q')
    (p : Q →ₗ[ℂ] P) (p' : Q' →ₗ[ℂ] P) (p₂ : Q →ₗ[ℂ] P₂) (p₂' : Q' →ₗ[ℂ] P₂)
    (o : S.map p = ⊤) (o' : S'.map p' = ⊤) (o₂ : S.map p₂ = ⊤) (o₂' : S'.map p₂' = ⊤)
    (k : ∀ x ∈ S, p x = 0 → p₂ x = 0) (k' : ∀ x ∈ S', p' x = 0 ↔ p₂' x = 0)
    (A : ι → S →ₗ[ℂ] Q) (A' : ι → S' → Q') (hA : ∀ i x, A i x ∈ S) (hA' : ∀ i x, A' i x ∈ S')
    (eq : ∀ i (x : S) (x' : S'), p x = p' x' → p (A i x) = p' (A' i x'))
    (eq₂ : ∀ i (x : S) (x' : S'), p₂ x = p₂' x' → p₂ (A i x) = p₂' (A' i x'))
    (irr : ∀ N : Submodule ℂ P, (∀ i (x : S), p x ∈ N → p (A i x) ∈ N) → N = ⊥ ∨ N = ⊤)
    (rk : Module.rank ℂ S ≤ Cardinal.aleph0) :
    ∃ (e : P →ₗ[ℂ] P₂) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ S, e (p x) = p₂ x) ∧ ∀ x ∈ S', e (p' x) = c • p₂' x := by
  have on : ∀ {Q P : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P] [Module ℂ P] {S : Submodule ℂ Q} {p : Q →ₗ[ℂ] P},
      S.map p = ⊤ → ∀ y, ∃ x : S, p x = y := fun {Q P} _ _ _ _ S p h y => by
    obtain ⟨x, hx, e⟩ : y ∈ S.map p := h ▸ Submodule.mem_top
    exact ⟨⟨x, hx⟩, e⟩
  obtain ⟨s, hs, hs'⟩ := exists_section p S
  obtain ⟨t, ht, ht'⟩ := exists_section p₂' S'
  have he : ∀ x ∈ S, p₂ (s (p x)) = p₂ x := fun x hx => by
    rw [← sub_eq_zero, ← map_sub]
    exact k _ (sub_mem (hs _) hx) (by rw [map_sub, hs' x hx, sub_self])
  have hd : ∀ x ∈ S', p' (t (p₂' x)) = p' x := fun x hx => by
    rw [← sub_eq_zero, ← map_sub]
    exact (k' _ (sub_mem (ht _) hx)).2 (by rw [map_sub, ht' x hx, sub_self])
  let ρ : ι → Module.End ℂ P := fun i => p ∘ₗ A i ∘ₗ s.codRestrict S hs
  have hρ : ∀ i (x : S), ρ i (p x) = p (A i x) := fun i x => by
    obtain ⟨x', hx'⟩ := on o' (p x)
    rw [eq i x x' hx'.symm]
    exact eq i ⟨s (p x), hs _⟩ x' ((hs' x x.2).trans hx'.symm)
  let U : Module.End ℂ P := p' ∘ₗ t ∘ₗ p₂ ∘ₗ s
  have hU : ∀ (x : S) (x' : S'), p₂ x = p₂' x' → U (p x) = p' x' := fun x x' h => by
    change p' (t (p₂ (s (p x)))) = _
    rw [he x x.2, h, hd x' x'.2]
  have rkP : Module.rank ℂ P ≤ Cardinal.aleph0 :=
    (LinearMap.rank_le_of_surjective (p.domRestrict S) fun y => on o y).trans rk
  obtain ⟨c, hc⟩ := GlobalTheory.dixmier_commutant_scalar ι P ρ rkP
    (fun N hN => irr N fun i x hx => hρ i x ▸ hN i _ hx) U fun i => LinearMap.ext fun y => by
      obtain ⟨x, rfl⟩ := on o y
      obtain ⟨x', hx'⟩ := on o₂' (p₂ x)
      obtain ⟨x₃, h₃⟩ := on o (p' x')
      rw [Module.End.mul_apply, Module.End.mul_apply, hρ, hU x x' hx'.symm, ← h₃, hρ, eq i x₃ x' h₃]
      exact hU ⟨_, hA i x⟩ ⟨_, hA' i x'⟩ (eq₂ i x x' hx'.symm)
  have main : ∀ (x : S) (x' : S'), p x = p' x' → p₂ x = c • p₂' x' := fun x x' h => by
    obtain ⟨y, hy⟩ := on o₂' (p₂ x)
    have h1 := hU x y hy.symm
    rw [hc, LinearMap.smul_apply, Module.End.one_apply, h] at h1
    have h2 := (k' _ (sub_mem y.2 (S'.smul_mem c x'.2))).1 (by rw [map_sub, map_smul, h1, sub_self])
    rw [map_sub, map_smul, sub_eq_zero] at h2
    rw [← hy, h2]
  refine ⟨p₂ ∘ₗ s, c, fun h0 => ?_, he, fun x' hx' => ?_⟩
  · obtain ⟨y, hy⟩ := exists_ne (0 : P₂)
    obtain ⟨x, rfl⟩ := on o₂ y
    obtain ⟨x', hx'⟩ := on o' (p x)
    exact hy (by rw [main x x' hx'.symm, h0, zero_smul])
  · obtain ⟨x, hx⟩ := on o (p' x')
    rw [← hx]
    exact (he x x.2).trans (main x ⟨x', hx'⟩ hx)

theorem countable_compactOpen (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] :
    {K : Set Y | IsCompact K ∧ IsOpen K}.Countable := by
  have hb := TopologicalSpace.isBasis_countableBasis Y
  refine ((Set.countable_setOf_finite_subset (TopologicalSpace.countable_countableBasis Y)).image fun s => ⋃₀ s).mono ?_
  rintro K ⟨h1, h2⟩
  obtain ⟨S, hS, rfl⟩ := hb.open_eq_sUnion h2
  obtain ⟨t, ht, hf, hc⟩ := h1.elim_finite_subcover_image (b := S) (c := id) (fun u hu => hb.isOpen (hS hu))
    (by rw [Set.sUnion_eq_biUnion]; rfl)
  refine ⟨t, ⟨hf, ht.trans hS⟩, Set.Subset.antisymm (Set.sUnion_mono ht) ?_⟩
  show ⋃₀ S ⊆ ⋃₀ t
  rw [Set.sUnion_eq_biUnion (s := t)]; exact hc

theorem rank_SB (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] :
    Module.rank ℂ (GlobalTheory.WeilM.SB Y) ≤ Cardinal.aleph0 := by
  classical
  let I : Set (Y → ℂ) := (fun K => Set.indicator K 1) '' {K : Set Y | IsCompact K ∧ IsOpen K}
  have hle : GlobalTheory.WeilM.SB Y ≤ Submodule.span ℂ I := by
    rintro f ⟨h1, h2⟩
    have hs : IsCompact (Function.support f) :=
      h2.of_isClosed_subset (h1.isClopen_fiber 0).compl.isClosed (subset_tsupport f)
    have fin : (f '' Function.support f).Finite := by
      obtain ⟨t, ht⟩ := hs.elim_finite_subcover (fun c : ℂ => f ⁻¹' {c}) (fun c => (h1.isClopen_fiber c).isOpen)
        fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩
      refine t.finite_toSet.subset ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, hc, e⟩ := Set.mem_iUnion₂.1 (ht hx)
      rw [show f x = c from e]; exact hc
    have e : f = ∑ c ∈ fin.toFinset, c • Set.indicator (f ⁻¹' {c}) 1 := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply, Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff,
        Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Set.Finite.mem_toFinset]
      split_ifs with h
      · rfl
      · by_contra h0; exact h ⟨x, h0, rfl⟩
    rw [e]
    refine sum_mem fun c hc => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨?_, (h1.isClopen_fiber c).isOpen⟩, rfl⟩)
    obtain ⟨x, hx, rfl⟩ := (Set.Finite.mem_toFinset _).1 hc
    exact hs.of_isClosed_subset (h1.isClopen_fiber _).isClosed fun y hy => by
      rw [Function.mem_support, show f y = f x from hy]; exact hx
  refine (Submodule.rank_mono hle).trans ((rank_span_le I).trans ?_)
  exact Cardinal.le_aleph0_iff_set_countable.2 ((countable_compactOpen Y).image _)

end PositivityTheory.ThKF

end
end

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem re_mul {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] {ev : AF F → R} {g k : UA σ Y.J} (hg : g ∈ UAt σ Y ev)
    (hk : k ∈ UAt σ Y ev) : g * k ∈ UAt σ Y ev := fun u hu => by
  have e : mat (g * k) - 1 = mat g * (mat k - 1) + (mat g - 1) := by
    rw [show mat (g * k) = mat g * mat k from rfl, Matrix.mul_sub, Matrix.mul_one]; abel
  rw [e, smul_add, hg u hu, ← Matrix.mul_smul, hk u hu, Matrix.mul_zero, add_zero]

theorem re_inv {m : ℕ} {Y : Spc F E m} {R : Type} [Zero R] {ev : AF F → R} {g : UA σ Y.J} (hg : g ∈ UAt σ Y ev) :
    g⁻¹ ∈ UAt σ Y ev := fun u hu => by
  have h1 : mat g⁻¹ * mat g = 1 := by rw [← show mat (g⁻¹ * g) = mat g⁻¹ * mat g from rfl, inv_mul_cancel]; rfl
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [Matrix.mul_sub, h1, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

theorem conj_line {m : ℕ} {Y : Spc F E m} {g : UA σ Y.J} (hg : g ∈ UAt σ Y (evI F)) {γ} (hγ : γ ∈ Lines σ Y) :
    (MulAut.conj g).toMonoidHom.comp γ ∈ Lines σ Y :=
  ⟨show Continuous fun t => g * γ t * g⁻¹ from (continuous_const.mul hγ.1).mul continuous_const,
    fun t => re_mul (re_mul hg (hγ.2 t)) (re_inv hg)⟩

theorem commute_conj {G M : Type} [Group G] [Monoid M] (φ : G →* M) {g k : G} {t t₂ : M} (h : φ g * t₂ = t * φ g)
    (hk : Commute (φ k) t₂) : Commute (φ (g * k * g⁻¹)) t := by
  have h' : φ g⁻¹ * t = t₂ * φ g⁻¹ := by
    calc φ g⁻¹ * t = φ g⁻¹ * (t * φ g) * φ g⁻¹ := by rw [mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = t₂ * φ g⁻¹ := by rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  show _ * t = t * _
  rw [map_mul, map_mul, mul_assoc, h', ← mul_assoc, mul_assoc (φ g), hk.eq, ← mul_assoc, h]
  simp only [mul_assoc]

theorem cj1 {G H : Type} [Group G] [Group H] (g x : G) (h : H) : (g * x * g⁻¹, (1 : H)) * (g, h) = (g, h) * (x, 1) := by simp

theorem cj2 {G H : Type} [Group G] [Group H] (g : G) (h x : H) : ((1 : G), h * x * h⁻¹) * (g, h) = (g, h) * (1, x) := by simp

theorem cj3 {G H : Type} [Group G] [Group H] (g : G) (h x : H) : ((1 : G), x) * (g, h) = (g, h) * (1, h⁻¹ * x * h⁻¹⁻¹) := by
  simp [mul_assoc]

theorem inv_rel {G M : Type} [Group G] [Monoid M] (φ : G →* M) {g : G} {t t₂ : M} (h : φ g * t₂ = t * φ g) :
    φ g⁻¹ * t = t₂ * φ g⁻¹ := by
  calc φ g⁻¹ * t = φ g⁻¹ * (t * φ g) * φ g⁻¹ := by rw [mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = t₂ * φ g⁻¹ := by rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

def matC {m : ℕ} (J : Matrix (Fin m) (Fin m) E) {w : InfinitePlace F} (τ : EmbOver E w) : UA σ J →* Matrix (Fin m) (Fin m) ℂ :=
  (piInf τ).mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp (Subgroup.subtype _))

def Moves (B : Base F E) {m : ℕ} (Y Y₂ : Spc F E m) (g : UA σ Y.J) : Prop :=
  g ∈ UAt σ Y (evI F) ∧ ∀ w, (mat g).map (piInf (B.emb w)) * Y₂.θ w = Y.θ w * (mat g).map (piInf (B.emb w))

theorem Moves.up {B : Base F E} {m : ℕ} {Y Y₂ : Spc F E m} {g : UA σ Y.J} (h : Moves B Y Y₂ g) {k : UA σ Y.J}
    (hk : k ∈ KInf σ (reS Y Y₂) B.emb) : g * k * g⁻¹ ∈ KInf σ Y B.emb :=
  ⟨re_mul (re_mul h.1 hk.1) (re_inv h.1), fun w => commute_conj (matC Y.J (B.emb w)) (h.2 w) (hk.2 w)⟩

theorem Moves.down {B : Base F E} {m : ℕ} {Y Y₂ : Spc F E m} {g : UA σ Y.J} (h : Moves B Y Y₂ g) {k : UA σ Y.J}
    (hk : k ∈ KInf σ Y B.emb) : g⁻¹ * k * g⁻¹⁻¹ ∈ KInf σ (reS Y Y₂) B.emb :=
  ⟨re_mul (Y := Y) (re_mul (re_inv h.1) hk.1) (re_inv (re_inv h.1)),
    fun w => commute_conj (matC Y.J (B.emb w)) (inv_rel (matC Y.J (B.emb w)) (h.2 w)) (hk.2 w)⟩

section Pair

variable {n d : ℕ} {X X₂ : Spc F E n} {W W₂ : Spc F E d} {B : Base F E} {M : Model σ X W} {M₂ : Model σ (reS X X₂) (reS W W₂)}
  {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem transK (hO : ArchOp) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') {g h T} (hT : IsArchOp om (g, h) T)
    {x₁ x₂ y₁ y₂} (h1 : x₁ ∈ UAt σ X (evI F)) (h2 : x₂ ∈ UAt σ W (evI F)) (e : (x₁, x₂) * (g, h) = (g, h) * (y₁, y₂))
    {f f₁ : SInf F (Fin n × Fin d)} (ha : Acts (evI F) (om (y₁, y₂)) f f₁) : Acts (evI F) (om (x₁, x₂)) (T f) (T f₁) := by
  obtain ⟨T₁, hT₁, -⟩ := hO F E σ B n d X W M χX χW om r s r' s' hp x₁ h1 x₂ h2
  have a := acts_comp hp (hT.2 f) (hT₁.2 (T f))
  rw [e] at a
  rw [(hQ F _ f _ _).1 _ (acts_comp hp ha (hT.2 f₁)) a]
  exact hT₁.2 _

theorem transL (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s')
    (hp₂ : IsPair B M₂ χX χW om r s r' s') {g h T} (hT : IsArchOp om (g, h) T)
    (hP : (M₂.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = M.Pol B.ψ B.emb) {γ δ γ₂ δ₂} (hγ : γ ∈ Lines σ X) (hδ : δ ∈ Lines σ W)
    (hγ₂ : γ₂ ∈ Lines σ X) (hδ₂ : δ₂ ∈ Lines σ W) (e : ∀ t, (γ t, δ t) * (g, h) = (g, h) * (γ₂ t, δ₂ t))
    {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M₂.Pol B.ψ B.emb)
    (ha : ActsD (evI F) (fun t => om (γ₂ (Multiplicative.ofAdd t), δ₂ (Multiplicative.ofAdd t))) f f₁) :
    ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), δ (Multiplicative.ofAdd t))) (T f) (T f₁) := by
  have hO' := hO
  choose op hop _ using hO F E σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨z, -, z2, z3⟩ := hL F E σ B n d _ _ M₂ χX χW om r s r' s' hp₂ γ₂ hγ₂ δ₂ hδ₂
    (fun t => op _ (hγ₂.2 _) _ (hδ₂.2 _)) (fun t => hop _ _ _ _) f hf
  obtain ⟨y, -, y2, y3⟩ := hL F E σ B n d X W M χX χW om r s r' s' hp γ hγ δ hδ
    (fun t => op _ (hγ.2 _) _ (hδ.2 _)) (fun t => hop _ _ _ _) (T f) (hP ▸ ⟨f, hf, rfl⟩)
  rw [(hQ F _ f f₁ z).2 _ ha z2, sinf_ext (f := T z) (g := y) fun L => ?_]
  · exact y2
  refine HasDerivAt.unique (z3 (L.comp T)) ?_
  refine (y3 L).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  exact congrArg L ((hQ F _ _ _ _).1 _ (transK hO' hQ hp hT (hγ.2 _) (hδ.2 _) (e _) ((hop _ _ _ _).2 f)) ((hop _ _ _ _).2 _))

theorem quot_trans (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s')
    (hp₂ : IsPair B M₂ χX χW om r s r' s') {g h T} (hg : Moves B X X₂ g) (hT : IsArchOp om (g, h) T)
    (hP : (M₂.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = M.Pol B.ψ B.emb) {P : Type} [AddCommGroup P] [Module ℂ P]
    {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P} (q : RealQuot B M om p) : RealQuot B M₂ om (p ∘ₗ (T : _ →ₗ[ℂ] _)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Submodule.map_comp, hP, q.onto]
  · exact fun γ hγ f hf f₁ ha => q.lie _ (conj_line hg.1 hγ) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
      (transL hO hL hQ hp hp₂ hT hP (conj_line hg.1 hγ) one_line hγ one_line (fun t => cj1 g (γ t) h) hf ha)
  · exact fun k hk f hf f₁ ha => q.cpt _ (hg.up hk) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
      (transK hO hQ hp hT (hg.up hk).1 (one_at _) (cj1 g k h) ha)

theorem exists_linop (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hp : IsPair B M χX χW om r s r' s') (i) :
    ∃ A : M.Pol B.ψ B.emb →ₗ[ℂ] SInf F (Fin n × Fin d), ∀ x, A x ∈ M.Pol B.ψ B.emb ∧ ∀ y, RInf B om i x y ↔ y = A x := by
  choose op hop hopP using hO F E σ B n d X W M χX χW om r s r' s' hp
  rcases i with δ | k
  · choose D h3 h4 h5 using hL F E σ B n d X W M χX χW om r s r' s' hp 1 one_line δ δ.2
      (fun t => op 1 (one_at _) _ (δ.2.2 _)) fun t => hop 1 _ _ _
    refine ⟨{ toFun := fun x => D x x.2
              map_add' := fun x y => sinf_ext fun L => ?_
              map_smul' := fun c x => sinf_ext fun L => ?_ }, fun x => ⟨h3 x x.2, fun y =>
      ⟨fun h => ((hQ F _ x.1 (D x x.2) y).2 _ (h4 x x.2) h).symm, fun h => by rw [h]; exact h4 x x.2⟩⟩⟩
    · refine (h5 _ (x + y).2 L).unique ?_
      simp only [Submodule.coe_add, map_add (f := _)]
      exact (h5 x x.2 L).add (h5 y y.2 L)
    · refine (h5 _ (c • x).2 L).unique ?_
      simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
      exact (h5 x x.2 L).const_smul c
  · exact ⟨(op 1 (one_at _) k k.2.1 : _ →ₗ[ℂ] _) ∘ₗ Submodule.subtype _, fun x => ⟨hopP 1 _ k _ (one_kinf _) k.2 x x.2, fun y =>
      ⟨fun h => ((hQ F _ x.1 _ y).1 _ ((hop 1 (one_at _) k k.2.1).2 x) h).symm,
        fun h => by rw [h]; exact (hop 1 (one_at _) k k.2.1).2 x⟩⟩⟩

end Pair

end PositivityTheory.ThKF

end
end

noncomputable section

namespace PositivityTheory.ThKF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem ker_of_eq {Q P P₂ : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P] [Module ℂ P] [AddCommGroup P₂] [Module ℂ P₂]
    {S : Submodule ℂ Q} {p : Q →ₗ[ℂ] P} {p₂ : Q →ₗ[ℂ] P₂} (h : LinearMap.ker p ⊓ S = LinearMap.ker p₂ ⊓ S) :
    ∀ x ∈ S, p x = 0 ↔ p₂ x = 0 := fun x hx =>
  ⟨fun h0 => (h ▸ (⟨h0, hx⟩ : x ∈ LinearMap.ker p ⊓ S) : x ∈ LinearMap.ker p₂ ⊓ S).1,
    fun h0 => (h.symm ▸ (⟨h0, hx⟩ : x ∈ LinearMap.ker p₂ ⊓ S) : x ∈ LinearMap.ker p ⊓ S).1⟩

theorem max_uniq {α : Type} [SemilatticeSup α] {St : α → Prop} {S N N' : α} (hs : St (N ⊔ N'))
    (h : N ≠ S → N' ≠ S → N ⊔ N' ≠ S) (h1 : Maximal (fun P => St P ∧ P ≠ S) N) (h2 : Maximal (fun P => St P ∧ P ≠ S) N') :
    N = N' :=
  le_antisymm (le_sup_left.trans (h2.2 ⟨hs, h h1.1.2 h2.1.2⟩ le_sup_right)) (le_sup_right.trans (h1.2 ⟨hs, h h1.1.2 h2.1.2⟩ le_sup_left))

theorem real_trans (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) {R : RealMaps F a a'} {V V' W} (t : IsTriple B G X om om')
    (t₂ : IsTriple B (reG G V V' W) X om om') (r : IsRealMaps B G om om' R) {g g' h T T'} (hg : Moves B G.V V g)
    (hg' : Moves B G.V' V' g') (hh : Moves B G.W W h) (hT : IsArchOp om (g, h) T) (hT' : IsArchOp om' (g', h) T')
    (hP : ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = G.M.Pol B.ψ B.emb)
    (hP' : ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) = G.M'.Pol B.ψ B.emb) :
    IsRealMaps B (reG G V V' W) om om' ⟨R.Pi, R.p ∘ₗ (T : _ →ₗ[ℂ] _), R.p' ∘ₗ (T' : _ →ₗ[ℂ] _)⟩ := by
  have hecke_div {χ χ' : Chr F E} (h : IsHecke F E χ) (h' : IsHecke F E χ') : IsHecke F E (χ / χ') :=
    ⟨h.1.div' h'.1, fun x => by rw [MonoidHom.div_apply, h.2, h'.2, div_one]⟩
  have res_div {K : Subgroup (AF F)ˣ} {χ χ' : Chr F E} {m n k : ℕ} (h : ResEtaPow K χ m)
      (h' : ResEtaPow K χ' n) (e : k = m + n) : ResEtaPow K (χ / χ') k := fun x => by
    rw [MonoidHom.div_apply, Circle.coe_div, h, h', e]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg, inv_one]
  have pairV {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
      IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, hecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
      res_div h.chars.resβ h.chars.resα rfl, h.weil⟩
  have pairV' {G : Geo σ a a'} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
      IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
    ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, hecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
      res_div h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩
  have quot_trans {n d : ℕ} {Y Y₂ : Spc F E n} {Z Z₂ : Spc F E d}
      {M : Model σ Y Z} {M₂ : Model σ (reS Y Y₂) (reS Z Z₂)}
      {χY χZ : Chr F E} {o : Rep σ Y Z} {u v u' v' : ℕ}
      (hp : IsPair B M χY χZ o u v u' v') (hp₂ : IsPair B M₂ χY χZ o u v u' v')
      {g h T} (hg : Moves B Y Y₂ g) (hT : IsArchOp o (g, h) T)
      (hP : (M₂.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) = M.Pol B.ψ B.emb)
      {P : Type} [AddCommGroup P] [Module ℂ P] {p : SInf F (Fin n × Fin d) →ₗ[ℂ] P}
      (q : RealQuot B M o p) : RealQuot B M₂ o (p ∘ₗ (T : _ →ₗ[ℂ] _)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Submodule.map_comp, hP, q.onto]
    · exact fun γ hγ f hf f₁ ha => q.lie _ (conj_line hg.1 hγ) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
        (transL hO hL hQ hp hp₂ hT hP (conj_line hg.1 hγ) one_line hγ one_line (fun t => cj1 g (γ t) h) hf ha)
    · exact fun k hk f hf f₁ ha => q.cpt _ (hg.up hk) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T f₁)
        (transK hO hQ hp hT (hg.up hk).1 (one_at _) (cj1 g k h) ha)
  have p1 := pairV t
  have p2 := pairV' t
  have q1 := pairV t₂
  have q2 := pairV' t₂
  refine ⟨quot_trans p1 q1 hg hT hP r.quot, quot_trans p2 q2 hg' hT' hP' r.quot',
    fun γ hγ f hf f' hf' f₁ f₁' a1 a2 => r.lie _ (conj_line hh.1 hγ) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T' f') (hP' ▸ ⟨f', hf', rfl⟩) _ _
      (transL hO hL hQ p1 q1 hT hP one_line (conj_line hh.1 hγ) one_line hγ (fun t => cj2 g h (γ t)) hf a1)
      (transL hO hL hQ p2 q2 hT' hP' one_line (conj_line hh.1 hγ) one_line hγ (fun t => cj2 g' h (γ t)) hf' a2),
    fun k hk f hf f' hf' f₁ f₁' a1 a2 => r.cpt _ (hh.up hk) (T f) (hP ▸ ⟨f, hf, rfl⟩) (T' f') (hP' ▸ ⟨f', hf', rfl⟩) _ _
      (transK hO hQ p1 hT (one_at _) (hh.up hk).1 (cj2 g h k) a1) (transK hO hQ p2 hT' (one_at _) (hh.up hk).1 (cj2 g' h k) a2),
    r.nontriv, fun N h1 h2 => r.irred N (fun γ hγ f hf y e hp => ?_) fun k hk f hf y e hp => ?_⟩
  · obtain ⟨u, hu, rfl⟩ : f ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) := hP ▸ hf
    have l := conj_line (re_inv hh.1) hγ
    obtain ⟨z, -, hz⟩ := pol_lie hO hL hQ q1 one_line l hu
    have := transL hO hL hQ p1 q1 hT hP one_line hγ one_line l (fun t => cj3 g h (γ t)) hu ((hz z).2 rfl)
    rw [(hQ F _ _ y (T z)).2 _ e this]
    exact h1 _ l u hu z ((hz z).2 rfl) hp
  · obtain ⟨u, hu, rfl⟩ : f ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) := hP ▸ hf
    have l := hh.down hk
    obtain ⟨z, -, hz⟩ := pol_k hO hQ q1 (one_kinf _) l hu
    have := transK hO hQ p1 hT (one_at _) hk.1 (cj3 g h k) ((hz z).2 rfl)
    rw [(hQ F _ _ y (T z)).1 _ e this]
    exact h2 _ l u hu z ((hz z).2 rfl) hp

theorem I_move (hI : ILeft) {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {χ χ' : Chr F E} {o : Rep σ Y W}
    {r s r' s' : ℕ} (hp : IsPair B M χ χ' o r s r' s') {Φ} (hΦ : Φ ∈ schA F _) (g h x) :
    M.I o (o (g, h) Φ) x = M.I o Φ (x * h) := by
  rw [show (g, h) = ((g, 1) : UA σ Y.J × UA σ W.J) * (1, h) by simp, map_mul, Module.End.mul_apply,
    hI F E σ B n d Y W M χ χ' o r s r' s' hp _ (hp.weil.isUSplitting.pres _ _ hΦ), I_right]

theorem move_sum {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ} (hM : M.IsGood ψ) {o : Rep σ Y W} {x T}
    (hT : IsArchOp o x T) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ i v, φ i v ∈ SB _) (h2 : ∀ i, ∀ᶠ v in cofinite, φ i v = M.vac v) :
    o x (∑ i, pure (f i) (φ i)) = ∑ i, pure (T (f i)) (φ i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨g, hg, e⟩ := pure_eq_pureA hM (φ i) (h1 i) (h2 i)
  rw [e, e, hT.1 _ g hg]

theorem so_re (V V' W) : G.M'.So B.ψ B.τ₁ ≤ (reG G V V' W).M'.So B.ψ B.τ₁ := by
  refine Submodule.span_mono ?_
  rintro _ ⟨f, φ, h1, h2, ⟨h3, ι, h4, h5⟩, rfl⟩
  exact ⟨f, φ, h1, h2, ⟨h3, ι, ⟨h4.bij, h4.trans, h4.mult⟩, h5⟩, rfl⟩

end PositivityTheory.ThKF

end
