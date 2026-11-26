module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignFlatDictionaryAtOnePlaceLargeDepth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalPureTensorProductExpansionAllPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductDependsOnDataProduct

@[expose] public section

attribute [-instance] UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryRelativeBaseVacuaLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorSumProdLocalPureTensors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLocalIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLocalIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem pureTensor_oppArgs_local : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) (w : Pl D.host.E) (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid G t w).rank b.tgt)) (Fin ((locGrid G t w).rank b.src)) (Kw w) → ℂ) (x : ∀ i : Fin D.R.m, Mx D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank) (y : ∀ j : Fin D.R.m, Mx D (G.V (.grid D.R.m (j + 1))).rank (G.V (.grid D.R.m j)).rank), (locGrid G t w).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) φ (oppArgs t B w x y) = (∏ i : Fin D.R.m, φ (.ex i D.R.m) (B.coord t w (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ ((x i).map fun a => cpt w (toEAf D a)))) * ∏ j : Fin D.R.m, φ (.theta D.R.m j) (B.coord t w (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ ((y j).map fun a => cpt w (toEAf D a))) := by
  intro D T L sc G t B w φ x y
  show ((GlobalTheory.SplitFlip.oppositePath D.R.m).map fun b => φ b (oppArgs t B w x y b)).prod = _
  simp only [GlobalTheory.SplitFlip.oppositePath, List.map_append, List.prod_append, List.map_reverse,
    List.prod_reverse, List.map_map]
  rw [← List.map_coe_finRange_eq_range, List.map_map, List.map_map, ← Fin.prod_univ_def, ← Fin.prod_univ_def]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ => ?_ <;> simp [oppArgs]

theorem flipFin_local_identity : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (Φ : ch.G.Datum) (e : AE D) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → (∀ x y, (∀ i, IsHalf e (x i)) → (∀ j, IsHalf e (y j)) → (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y)) → ∀ (n : locPl ch.G t → ℕ) (xw : ∀ w : locPl ch.G t, Fin (n w) → ℂ) (φw : ∀ w : locPl ch.G t, Fin (n w) → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ (w : locPl ch.G t) z, Tflip ch.W ch.S.B t Φ w.1 z = ∑ i, xw w i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i) z) → ∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ Fintype.piFinset (fun w => (Finset.univ : Finset (Fin (n w)))), (∏ w, xw w (a w)) * (∏ i : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (x i)) * ∏ j : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (y j) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch t Φ e τ φ hloc hfac n xw φw hexp x y
  by_cases hh : (∀ i, IsHalf e (x i)) ∧ ∀ j, IsHalf e (y j)
  · rw [hfac x y hh.1 hh.2, ← Finset.prod_coe_sort]
    simp_rw [hexp, pureTensor_oppArgs_local]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hh.1, hh.2, ↓reduceIte, Finset.prod_mul_distrib]
    rw [mul_assoc]
    congr 2 <;> exact Finset.prod_comm
  · rw [not_and_or] at hh
    rcases hh with hh | hh <;> simp only [not_forall] at hh <;> obtain ⟨k, hk⟩ := hh
    · trans (0 : ℂ)
      · rw [Finsupp.sum]
        refine Finset.sum_eq_zero fun d hd => ?_
        have h0 : (φ d).1 k (x k) = 0 := by
          by_contra hne
          exact hk (((hloc d hd).1 k).1.1 (x k) hne)
        apply mul_eq_zero_of_left
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · symm
        refine Finset.sum_eq_zero fun a _ => ?_
        apply mul_eq_zero_of_left
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by dsimp only; exact if_neg hk)
    · trans (0 : ℂ)
      · rw [Finsupp.sum]
        refine Finset.sum_eq_zero fun d hd => ?_
        have h0 : (φ d).2 k (y k) = 0 := by
          by_contra hne
          exact hk (((hloc d hd).2 k).1.1 (y k) hne)
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) h0
      · symm
        refine Finset.sum_eq_zero fun a _ => ?_
        apply mul_eq_zero_of_right
        exact Finset.prod_eq_zero (Finset.mem_univ k) (by dsimp only; exact if_neg hk)

end GlobalTheory.LocAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLocalIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flippedFiniteTensor_local_identity : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (t : T) (Φ : ch.G.Datum) (e : AE D) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → (∀ x y, (∀ i, IsHalf e (x i)) → (∀ j, IsHalf e (y j)) → (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∏ w ∈ locPl ch.G t, Tflip ch.W ch.S.B t Φ w (oppArgs t ch.S.B w x y)) → ∀ (n : locPl ch.G t → ℕ) (xw : ∀ w : locPl ch.G t, Fin (n w) → ℂ) (φw : ∀ w : locPl ch.G t, Fin (n w) → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ (w : locPl ch.G t) z, Tflip ch.W ch.S.B t Φ w.1 z = ∑ i, xw w i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i) z) → ∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ Fintype.piFinset (fun w => (Finset.univ : Finset (Fin (n w)))), (∏ w, xw w (a w)) * (∏ i : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (x i)) * ∏ j : Fin D.R.m, (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (y j) := by
  first | exact @GlobalTheory.LocAsm.flipFin_local_identity | exact GlobalTheory.LocAsm.flipFin_local_identity | (intros; apply GlobalTheory.LocAsm.flipFin_local_identity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductFunctionEqOfLocalIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductFunctionEqOfLocalIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

theorem prodRel_map {ι I : Type} [Fintype ι] {X Y : ι → Type} (S : Finset I) (x : I → ℂ) (g : I → ∀ l, X l → ℂ)
    (T : ∀ l, (X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) (h : ∀ z : ∀ l, X l, ∑ i ∈ S, x i * ∏ l, g i l (z l) = 0) (y : ∀ l, Y l) :
    ∑ i ∈ S, x i * ∏ l, T l (g i l) (y l) = 0 := by
  have hkey : ∀ l, ∃ (s : Finset (X l)) (E : X l → X l → ℂ), (∀ x, E x ∈ (⊤ : Submodule ℂ (X l → ℂ))) ∧
      ∀ u ∈ S.image (fun i => g i l), u = ∑ x ∈ s, u x • E x := fun l =>
    GlobalTheory.finset_functions_recovered_from_values ⊤ _ (fun _ _ => Submodule.mem_top)
  choose s E _ hE using hkey
  have h1 : ∀ i ∈ S, ∏ l, T l (g i l) (y l) =
      ∑ ξ ∈ Fintype.piFinset s, (∏ l, g i l (ξ l)) * ∏ l, T l (E l (ξ l)) (y l) := by
    intro i hi
    have h2 : ∀ l, T l (g i l) (y l) = ∑ x ∈ s l, g i l x * T l (E l x) (y l) := by
      intro l
      conv_lhs => rw [hE l (g i l) (Finset.mem_image_of_mem _ hi)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finset.sum_apply]
    simp only [h2]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun i hi => by rw [h1 i hi, Finset.mul_sum], Finset.sum_comm]
  refine Finset.sum_eq_zero fun ξ _ => ?_
  simp only [← mul_assoc]
  rw [← Finset.sum_mul, h ξ, zero_mul]

theorem prodRel_allSome {ι I : Type} [Fintype ι] {X Y : ι → Type} (S : Finset I) (x : I → ℂ) (g : I → ∀ l, X l → ℂ)
    (f : I → ∀ l, Y l → ℂ) (Q : ∀ l, ((X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) → Prop)
    (hf : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q l) fun T => f i l = T (g i l))
    (h : ∀ z : ∀ l, X l, ∑ i ∈ S, x i * ∏ l, g i l (z l) = 0) (y : ∀ l, Y l) :
    ∑ i ∈ S, x i * ∏ l, f i l (y l) = 0 := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  choose T hT using fun l => (hf i₀ hi₀ l).1
  rw [← prodRel_map S x g T h y]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [fun l => (hf i hi l).2 _ (hT l)]

theorem prodRel_allSome₂ {ι κ I : Type} [Fintype ι] [Fintype κ] {X Y : ι → Type} {X' Y' : κ → Type} (S : Finset I) (x : I → ℂ)
    (g : I → ∀ l, X l → ℂ) (f : I → ∀ l, Y l → ℂ) (Q : ∀ l, ((X l → ℂ) →ₗ[ℂ] (Y l → ℂ)) → Prop)
    (g' : I → ∀ l, X' l → ℂ) (f' : I → ∀ l, Y' l → ℂ) (Q' : ∀ l, ((X' l → ℂ) →ₗ[ℂ] (Y' l → ℂ)) → Prop)
    (hf : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q l) fun T => f i l = T (g i l))
    (hf' : ∀ i ∈ S, ∀ l, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AllSome (Q' l) fun T => f' i l = T (g' i l))
    (h : ∀ (z : ∀ l, X l) (z' : ∀ l, X' l), ∑ i ∈ S, x i * ((∏ l, g i l (z l)) * ∏ l, g' i l (z' l)) = 0)
    (y : ∀ l, Y l) (y' : ∀ l, Y' l) :
    ∑ i ∈ S, x i * ((∏ l, f i l (y l)) * ∏ l, f' i l (y' l)) = 0 := by
  simp only [← mul_assoc]
  refine prodRel_allSome S (fun i => x i * ∏ l, f i l (y l)) g' f' Q' hf' (fun z' => ?_) y'
  have := prodRel_allSome S (fun i => x i * ∏ l, g' i l (z' l)) g f Q hf (fun z => by
    rw [← h z z']
    exact Finset.sum_congr rfl fun i _ => by ring) y
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem unfolded_eq_of_local_eq : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → ∀ (α : Type) (SA : Finset α) (xA : α → ℂ) (F : α → ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ) (Gd : α → ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) → ℂ) (fr : α → SchRow ch.G) (fd : α → SchDown ch.G t), (∀ a ∈ SA, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (F a i) (fr a i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (Gd a j) (fd a j)) → (∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ SA, xA a * (∏ i, F a i (x i)) * ∏ j, Gd a j (y j)) → ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R Fc _ ch _ _ hcon t e _ τ φ hτ α SA xA F Gd fr fd hA hloc M hM P h u y
  have key := hcon t M hM P h ((SchRow ch.G × SchDown ch.G t) ⊕ α) (τ.support.disjSum SA)
    (Sum.elim (fun d => τ d) fun a => -xA a) (Sum.elim (fun d => d.1) fr) (Sum.elim (fun d => d.2) fd) ?_ ?_ u y
  · rw [Finset.sum_disjSum] at key
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
    exact add_neg_eq_zero.mp key
  · intro i hi j
    have hv := (ch.rm.vT_is t D.R.m j le_rfl j.2).2.theta
    rcases i with d | a
    · exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt ch.W.ψ_std ch.W.θ_is ((hτ d (by simpa using hi)).2 j).2 hv
    · exact GlobalTheory.VecTheta.isThetaFunO_of_thetaAt ch.W.ψ_std ch.W.θ_is ((hA a (by simpa using hi)).2 j).2 hv
  · intro y v
    refine prodRel_allSome₂ (τ.support.disjSum SA) (Sum.elim (fun d => τ d) fun a => -xA a)
      (Sum.elim (fun d => (φ d).1) F) (Sum.elim (fun d => d.1) fr)
      (fun i => IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
        (latO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) (ch.G.latS (.chi i D.R.m : Pair T) : Set _)
          (ch.G.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) 1 (ch.rm.vX i D.R.m))
      (Sum.elim (fun d => (φ d).2) Gd) (Sum.elim (fun d => d.2) fd)
      (fun j => IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
        (latO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) (ch.G.latS (.mu t D.R.m j : Pair T) : Set _)
          (ch.G.latT (.mu t D.R.m j : Pair T) : Set _) fun _ => True) 1 (ch.rm.vT D.R.m j)) ?_ ?_ ?_ y v
    · intro i hi l
      rcases i with d | a
      · exact ((hτ d (by simpa using hi)).1 l).2
      · exact ((hA a (by simpa using hi)).1 l).2
    · intro i hi l
      rcases i with d | a
      · exact ((hτ d (by simpa using hi)).2 l).2
      · exact ((hA a (by simpa using hi)).2 l).2
    · intro z z'
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, ← mul_assoc]
      exact add_neg_eq_zero.mpr (hloc z z')

end GlobalTheory.LocAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductFunctionEqOfLocalIdentityStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedProductFunction_eq_of_local_identity : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ) (φ : SchRow ch.G × SchDown ch.G t → SchRow ch.G × SchDown ch.G t), (∀ d ∈ τ.support, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) ((φ d).1 i) (d.1 i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) ((φ d).2 j) (d.2 j)) → ∀ (α : Type) (SA : Finset α) (xA : α → ℂ) (F : α → ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ) (Gd : α → ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T)) → ℂ) (fr : α → SchRow ch.G) (fd : α → SchDown ch.G t), (∀ a ∈ SA, (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (F a i) (fr a i)) ∧ ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (Gd a j) (fd a j)) → (∀ (x : RowPt ch.G) (y : ∀ j : Fin D.R.m, WO (ch.G.pS (.mu t D.R.m j : Pair T)) (ch.G.pT (.mu t D.R.m j : Pair T))), (τ.sum fun d c => c * (∏ i, (φ d).1 i (x i)) * ∏ j, (φ d).2 j (y j)) = ∑ a ∈ SA, xA a * (∏ i, F a i (x i)) * ∏ j, Gd a j (y j)) → ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  first | exact @GlobalTheory.LocAsm.unfolded_eq_of_local_eq | exact GlobalTheory.LocAsm.unfolded_eq_of_local_eq | (intros; apply GlobalTheory.LocAsm.unfolded_eq_of_local_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumPureTensorOfIsTensorDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumPureTensorOfIsTensorDepth
open MeasureTheory GlobalTheory.FunObj

noncomputable section
namespace GlobalTheory.TensorExpansion
open GlobalTheory.SplitFlip ValuativeRel Matrix
open scoped Pointwise

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem unitsPowInv_val (ϖ : kˣ) (e : ℕ) : (((ϖ ^ e)⁻¹ : kˣ) : k) = ((ϖ : k) ^ e)⁻¹ := by
  simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]

theorem resMk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  have h0 : (ϖ : k) ^ e ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    unitsPowInv_val]
  constructor
  · rintro ⟨c, hc⟩
    have h1 : (a : k) - b = (ϖ : k) ^ e * c := by
      have := congrArg Subtype.val hc
      simpa using this
    rw [h1, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ h0, one_mul]

theorem mem_of_inv_mul_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {x : k}
    (h : (((ϖ ^ e)⁻¹ : kˣ) : k) * x ∈ 𝒪[k]) : x ∈ 𝒪[k] := by
  have hx : x = (ϖ : k) ^ e * ((((ϖ ^ e)⁻¹ : kˣ) : k) * x) := by
    rw [unitsPowInv_val, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul]
  rw [hx]
  exact mul_mem (pow_mem hϖ.mem _) h

theorem mem_matLat_pow_smul_iff (ϖ : kˣ) (e : ℕ) {m n : ℕ} {Z : Matrix (Fin m) (Fin n) k} :
    Z ∈ matLat (Fin m) (ϖ ^ e • stdLat k (Fin n)) ↔ ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j ∈ 𝒪[k] :=
  ⟨fun h i j => mem_stdLat.1 ((mem_smul_lat _ _ _).1 (h i)) j,
   fun h i => (mem_smul_lat _ _ _).2 (mem_stdLat.2 fun j => h i j)⟩

def resClass (ϖ : kˣ) {e : ℕ} {m n : ℕ} (c : Fin m → Fin n → Res k e) : Set (Matrix (Fin m) (Fin n) k) :=
  {X | ∀ i j, X i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) ∈ 𝒪[k]}

theorem isNatDatum_resClass {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {m n : ℕ} (c : Fin m → Fin n → Res k e) :
    IsNatDatum ϖ e ((resClass ϖ c).indicator (1 : Matrix (Fin m) (Fin n) k → ℂ)) := by
  classical
  refine ⟨fun X hX => Set.indicator_of_notMem (fun h => hX (mem_matLat_stdLat.2 fun i j => (h i j).1)) _,
    fun X Z hZ => ?_⟩
  have hZ' := (mem_matLat_pow_smul_iff ϖ e).1 hZ
  have hiff : X + Z ∈ resClass ϖ c ↔ X ∈ resClass ϖ c := by
    refine forall_congr' fun i => forall_congr' fun j => ?_
    have hz : Z i j ∈ 𝒪[k] := mem_of_inv_mul_mem hϖ e (hZ' i j)
    have h1 : (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j + Z i j - liftRes c i j) =
        (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) + (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j := by ring
    show (X i j + Z i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j + Z i j - liftRes c i j) ∈ 𝒪[k]) ↔
      (X i j ∈ 𝒪[k] ∧ (((ϖ ^ e)⁻¹ : kˣ) : k) * (X i j - liftRes c i j) ∈ 𝒪[k])
    rw [h1, add_mem_cancel_right hz, add_mem_cancel_right (hZ' i j)]
  simp only [Set.indicator_apply, hiff, Pi.one_apply]

theorem exists_sum_pureTensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by
  intro k _ _ _ _ G ϖ hϖ e γ T hT
  classical
  let L := γ.toFinset
  let I := ∀ b : L, Fin (G.rank b.1.tgt) → Fin (G.rank b.1.src) → Res k e
  let rep : I → G.Args := fun c b => if h : b ∈ L then liftRes (c ⟨b, h⟩) else 0
  let ψ : I → ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ :=
    fun c b => if h : b ∈ L then (resClass ϖ (c ⟨b, h⟩)).indicator 1 else 1
  have key : ∀ z, T z = ∑ c, T (rep c) * G.lines₂ γ (ψ c) z := by
    intro z
    simp only [Grid.lines₂]
    by_cases hint : ∀ b ∈ γ, z b ∈ matLat _ (stdLat k _)
    · let c0 : I := fun b i j => Ideal.Quotient.mk _
        ⟨z b.1 i j, mem_matLat_stdLat.1 (hint b.1 (List.mem_toFinset.1 b.2)) i j⟩
      have hmem : ∀ (c : I) (b : L), z b.1 ∈ resClass ϖ (c b) ↔ c b = c0 b := by
        intro c b
        have hz := mem_matLat_stdLat.1 (hint b.1 (List.mem_toFinset.1 b.2))
        constructor
        · intro h
          funext i j
          have := (resMk_eq_iff hϖ e ⟨z b.1 i j, hz i j⟩ (Quotient.out (c b i j))).2 (h i j).2
          rw [Ideal.Quotient.mk_out] at this
          exact this.symm
        · rintro h i j
          refine ⟨hz i j, ?_⟩
          exact (resMk_eq_iff hϖ e ⟨z b.1 i j, hz i j⟩ (Quotient.out (c b i j))).1
            (by rw [Ideal.Quotient.mk_out, h])
      rw [Finset.sum_eq_single c0]
      · have hprod : (γ.map fun b => ψ c0 b (z b)).prod = 1 := by
          refine List.prod_eq_one fun x hx => ?_
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
          have hb' : b ∈ L := List.mem_toFinset.2 hb
          simp only [ψ, dif_pos hb']
          exact Set.indicator_of_mem ((hmem c0 ⟨b, hb'⟩).2 rfl) _
        rw [hprod, mul_one]
        let w : G.Args := fun b => if b ∈ γ then z b - rep c0 b else 0
        have hw : ∀ b, w b ∈ matLat _ (ϖ ^ e • stdLat k _) := by
          intro b
          by_cases hb : b ∈ γ
          · have hb' : b ∈ L := List.mem_toFinset.2 hb
            have h2 := (hmem c0 ⟨b, hb'⟩).2 rfl
            refine (mem_matLat_pow_smul_iff ϖ e).2 fun i j => ?_
            simp only [w, if_pos hb, rep, dif_pos hb', Matrix.sub_apply]
            exact (h2 i j).2
          · simp only [w, if_neg hb]
            exact zero_mem _
        rw [← hT.2.2 (rep c0) w hw]
        refine hT.1 fun b hb => ?_
        have hb : b ∈ γ := hb
        simp [w, hb]
      · intro c _ hc
        obtain ⟨b, hb⟩ : ∃ b : L, c b ≠ c0 b := by
          by_contra hne
          push_neg at hne
          exact hc (funext hne)
        rw [List.prod_eq_zero (List.mem_map.2 ⟨b.1, List.mem_toFinset.1 b.2, ?_⟩), mul_zero]
        simp only [ψ, dif_pos b.2]
        exact Set.indicator_of_notMem (mt (hmem c b).1 hb) _
      · intro h
        exact absurd (Finset.mem_univ _) h
    · push_neg at hint
      obtain ⟨b, hb, hz⟩ := hint
      rw [hT.2.1 z b hb hz]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      rw [List.prod_eq_zero (List.mem_map.2 ⟨b, hb, ?_⟩), mul_zero]
      have hb' : b ∈ L := List.mem_toFinset.2 hb
      simp only [ψ, dif_pos hb']
      have hn : z b ∉ resClass ϖ (c ⟨b, hb'⟩) := fun h =>
        hz (mem_matLat_stdLat.2 fun i j => (h i j).1)
      exact Set.indicator_of_notMem hn _
  refine ⟨Fintype.card I, fun i => T (rep ((Fintype.equivFin I).symm i)),
    fun i => ψ ((Fintype.equivFin I).symm i), ?_, ?_⟩
  · intro i b hb
    have hb' : b ∈ L := List.mem_toFinset.2 hb
    simp only [ψ, dif_pos hb']
    exact isNatDatum_resClass hϖ e _
  · intro z
    rw [key z]
    exact (Equiv.sum_comp (Fintype.equivFin I).symm (fun c => T (rep c) * G.lines₂ γ (ψ c) z)).symm

end GlobalTheory.TensorExpansion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumPureTensorOfIsTensorDepthStatement
open MeasureTheory GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_pureTensor_of_isTensor_depth : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by
  first | exact @GlobalTheory.TensorExpansion.exists_sum_pureTensor | exact GlobalTheory.TensorExpansion.exists_sum_pureTensor | (intros; apply GlobalTheory.TensorExpansion.exists_sum_pureTensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMovedTensorFinsetSumLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMovedTensorFinsetSumLinear
open MeasureTheory GlobalTheory.FunObj

namespace GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

theorem flatTensor_moved_sum {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s)
    (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (hψ : Continuous ψ) (ϖ : kˣ) (e : ℕ) (keep : Bool)
    (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ)
    (hT : ∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) (X : ColArgs G) (Y : RowArgs G) :
    flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y =
      ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  classical
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hint : ∀ i ∈ S, Integrable (flatIntegrand hs ψ (moved G keep g (T i)) X Y) (varsVol G ν) := by
    intro i hi
    unfold varsVol
    exact (continuous_flatIntegrand hs hψ (hT i hi) keep g X Y).integrable_of_hasCompactSupport
      (hasCompactSupport_flatIntegrand hs ψ (hT i hi) keep g X Y)
  have h : ∀ v, flatIntegrand hs ψ (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y v =
      ∑ i ∈ S, x i * flatIntegrand hs ψ (moved G keep g (T i)) X Y v := by
    intro v
    simp only [flatIntegrand, moved, GlobalTheory.SplitFlip.Grid.pathAct, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [flatTensor, h]
  rw [MeasureTheory.integral_finsetSum _ fun i hi => (hint i hi).const_mul _]
  simp only [integral_const_mul]

end GlobalTheory.FunObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorMovedTensorFinsetSumLinearStatement
open MeasureTheory GlobalTheory.FunObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure], Continuous ψ → ∀ (ϖ : kˣ) (e : ℕ) (keep : Bool) (g : G.VertexGroup) {ι : Type} (S : Finset ι) (x : ι → ℂ) (T : ι → G.Args → ℂ), (∀ i ∈ S, G.IsTensor ϖ e (GlobalTheory.SplitFlip.oppositePath G.m) (T i)) → ∀ X Y, flatTensor hs ψ ν (moved G keep g (fun z => ∑ i ∈ S, x i * T i z)) X Y = ∑ i ∈ S, x i * flatTensor hs ψ ν (moved G keep g (T i)) X Y := by
  first | exact @GlobalTheory.FunObj.flatTensor_moved_sum | exact GlobalTheory.FunObj.flatTensor_moved_sum | (intros; apply GlobalTheory.FunObj.flatTensor_moved_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorSumProdLocalPureTensors
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open GlobalTheory.FlipRun
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LocAsm

theorem continuous_psiAt_locPl : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T), ∀ w ∈ locPl ch.G t, Continuous (psiAt ch.W w) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t w hw
  have hL := s.core.lev
  have hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
    obtain ⟨⟨P, -, -⟩, -⟩ := s.size
    have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
      UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
    exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde (hch.guard t)).1 w hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  exact (hg.square 0 hm 0 hm).cond.continuous

theorem flipFin_productExpansion : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (Φ : ch.G.Datum) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ), IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (β : CosFam ch.G t) (e : AE D), IsIdemSum e (locPl ch.G t) → ∃ (α : Type) (SA : Finset α) (xA : α → ℂ) (φ : α → (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fd : α → SchDown ch.G t) (fr : α → SchRow ch.G), (∀ a ∈ SA, ∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ a w b)) ∧ (∀ a ∈ SA, (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ a w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd a j)) ∧ (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ a w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr a i))) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → ∏ w, (ch.S.term t Φ β w).datum (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = ∑ a ∈ SA, xA a * ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ a w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  have H := (isTensor_flips_take.and GlobalTheory.T.last_row_column_product_data_have_vectors).and (GlobalTheory.T.unfoldedProductFunction_eq_of_local_identity.and continuous_psiAt_locPl)
  refine big_mono ?_ H
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h
  obtain ⟨⟨hTen, hVec⟩, hCon, hψ⟩ := h
  intro hCL t Φ τ hFF β e he
  have hexp : ∀ w : locPl ch.G t, ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ), (∀ i, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ i b)) ∧ ∀ z, Tflip ch.W ch.S.B t Φ w.1 z = ∑ i, x i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ i) z := by
    intro w
    have h1 := hTen t Φ w.1 w.2 (D.R.m ^ 2) le_rfl
    rw [List.take_of_length_le (le_of_eq (canFlip_flipOrder D.R.m).2.1)] at h1
    have hp := (flipStage_path_level t w.1 ch.S.B ch.W Φ).1
    change (locGrid ch.G t w.1).IsTensor _ _ (flipStage t w.1 ch.S.B ch.W Φ).path (Tflip ch.W ch.S.B t Φ w.1) at h1
    rw [hp] at h1
    exact GlobalTheory.T.exists_sum_pureTensor_of_isTensor_depth _ _ (isUnif_unifAt w.1) _ _ _ h1
  choose n xw φw hnat hTeq using hexp
  have hv := fun a : (∀ w : locPl ch.G t, Fin (n w)) => hVec t e he (fun w => φw w (a w)) (fun w b hb => hnat w (a w) b hb)
  choose fd hfd using fun a j => (hv a).1 j
  choose fr hfr using fun a i => (hv a).2 i
  refine ⟨∀ w : locPl ch.G t, Fin (n w), Fintype.piFinset (fun w => Finset.univ), fun a => ∏ w, xw w (a w), fun a w => φw w (a w), fd, fr, ?_, ?_, ?_, ?_⟩
  · intro a _ w b hb
    exact hnat w (a w) b hb
  · intro a _
    exact ⟨hfd a, hfr a⟩
  · intro u y _ _
    have key : ∀ w : locPl ch.G t, (ch.S.term t Φ β w).datum (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = ∑ i, xw w i * flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) := by
      intro w
      haveI := (isUnitVol_unitVol w.1).1
      have hT : Tflip ch.W ch.S.B t Φ w.1 = fun z => ∑ i ∈ Finset.univ, xw w i * (locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φw w i) z := funext (hTeq w)
      show flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) (Tflip ch.W ch.S.B t Φ w.1)) _ _ = _
      rw [hT]
      exact GlobalTheory.T.flatTensor_movedTensor_finset_sum_linear _ one_le_sLen _ _ (hψ t w.1 w.2) (unifAt w.1) (depthAt ch.G w.1) _ _ _ _ _ (fun i _ => (locGrid ch.G t w.1).isTensor_pureTensor _ _ _ _ (hnat w i)) _ _
    simp only [key]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.prod_mul_distrib]
  · obtain ⟨e', he', φ', hφ', hid⟩ := hFF
    obtain rfl := GlobalTheory.IdemSumUniq.idemSum_unique _ _ _ he he'
    intro M hM P h u y
    refine hCon hCL t e he τ φ' hφ' (∀ w : locPl ch.G t, Fin (n w)) (Fintype.piFinset fun w => Finset.univ) (fun a => ∏ w, xw w (a w)) (fun a i => (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0)) (fun a j => (fun y => if IsHalf e y then ∏ w : locPl ch.G t, (fun w => φw w (a w)) w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0)) fr fd ?_ ?_ M hM P h u y
    · intro a _
      exact ⟨hfr a, hfd a⟩
    · exact GlobalTheory.T.flippedFiniteTensor_local_identity ch t Φ e τ φ' hφ' hid n xw φw hTeq

end GlobalTheory.LocAsm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorSumProdLocalPureTensorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flippedFiniteTensor_sum_prod_local_pure_tensors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ConLin ch → ∀ (t : T) (Φ : ch.G.Datum) (τ : SchRow ch.G × SchDown ch.G t →₀ ℂ), IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (β : CosFam ch.G t) (e : AE D), IsIdemSum e (locPl ch.G t) → ∃ (α : Type) (SA : Finset α) (xA : α → ℂ) (φ : α → (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fd : α → SchDown ch.G t) (fr : α → SchRow ch.G), (∀ a ∈ SA, ∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ a w b)) ∧ (∀ a ∈ SA, (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ a w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd a j)) ∧ (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ a w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr a i))) ∧ (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))), (∀ j, IsHalf e (u j)) → (∀ i, IsHalf e (y i)) → ∏ w, (ch.S.term t Φ β w).datum (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y) = ∑ a ∈ SA, xA a * ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (φ a w))) (ch.S.colAt t w.1 u) (ch.S.rowAt t w.1 y)) ∧ ∀ (M : Vol ch.G) (hM : M.Is t) (P : PolDown ch.G) (h : Pts ch.G) (u : ColPt ch.G) (y : RowPt ch.G), (τ.sum fun d x => x * evT (conAt ch.W hM (fockD ch.W t d.2 P) h) d.1 u y) = ∑ a ∈ SA, xA a * evT (conAt ch.W hM (fockD ch.W t (fd a) P) h) (fr a) u y := by
  first | exact @GlobalTheory.LocAsm.flipFin_productExpansion | exact GlobalTheory.LocAsm.flipFin_productExpansion | (intros; apply GlobalTheory.LocAsm.flipFin_productExpansion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCombinationDependsOnProductFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCombinationDependsOnProductFunction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CombDet

theorem row_position {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T} {p : Pair T}
    {I : Type} (S : Finset I) (e : AE D) (d : I → FinDatum G t p) (c : I → (WO (G.pS p) (G.pT p) →₀ ℂ))
    (hd : ∀ i ∈ S, (d i).e = e ∧ IsCombOf W (d i) (c i)) (f₀ : WO (G.pS p) (G.pT p) → ℂ)
    (h1 : IsThetaFunO W.ψ _ _ f₀)
    (h2 : IsLatVac (heisO W.ψ _ _) (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) f₀) :
    ∃ Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ), ∀ i ∈ S, comb W.ψ _ _ (c i) f₀ = Tm (d i).fn := by
  rcases S.eq_empty_or_nonempty with hS | ⟨i₀, hi₀⟩
  · exact ⟨0, fun i hi => by simp [hS] at hi⟩
  have key : ∀ i ∈ S, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) e
      (latO (G.pS p) (G.pT p) (G.latS p : Set _) (G.latT p : Set _) fun _ => True) 1 f₀ (d i).fn (comb W.ψ _ _ (c i) f₀) := by
    intro i hi
    have h := (hd i hi).2.2.2 f₀ h1 h2
    have he := (hd i hi).1
    unfold FinDatum.IsTheta at h
    rw [he] at h
    exact h
  obtain ⟨Tm, hTm⟩ := (key i₀ hi₀).1
  exact ⟨Tm, fun i hi => (key i hi).2 Tm hTm⟩

def Spans {I Y : Type} (S : Finset I) (H : Y → I → ℂ) (g : I → ℂ) : Prop :=
  ∃ (J : Type) (P : Finset J) (a : J → ℂ) (y : J → Y), ∀ i ∈ S, g i = ∑ j ∈ P, a j * H (y j) i

theorem sum_prod_eq_zero {I ι : Type} [Fintype ι] {Y : ι → Type} (S : Finset I) (x : I → ℂ) (H : ∀ l, Y l → I → ℂ)
    (g : ι → I → ℂ) (hg : ∀ l, Spans S (H l) (g l)) (h : ∀ z : ∀ l, Y l, ∑ i ∈ S, x i * ∏ l, H l (z l) i = 0) :
    ∑ i ∈ S, x i * ∏ l, g l i = 0 := by
  classical
  choose J P a y hy using hg
  have e : ∀ i ∈ S, x i * ∏ l, g l i =
      ∑ z ∈ Fintype.piFinset P, (∏ l, a l (z l)) * (x i * ∏ l, H l (y l (z l)) i) := by
    intro i hi
    rw [Finset.prod_congr rfl fun l _ => hy l i hi, Finset.prod_univ_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  refine Finset.sum_eq_zero fun z _ => ?_
  rw [← Finset.mul_sum, h fun l => y l (z l), mul_zero]

theorem reproducing {I X : Type} (S : Finset I) (V : Submodule ℂ (X → ℂ)) (F : I → X → ℂ) (hF : ∀ i ∈ S, F i ∈ V) :
    ∃ (P : Finset X) (u : X → X → ℂ), (∀ x, u x ∈ V) ∧ ∀ i ∈ S, F i = ∑ x ∈ P, F i x • u x := by
  classical
  obtain ⟨P, u, hu⟩ := GlobalTheory.exists_finite_reproducing_of_submodule V
    (S.attach.image fun i : {i // i ∈ S} => (⟨F i.1, hF i.1 i.2⟩ : V))
  refine ⟨P, fun x => u x, fun x => (u x).2, fun i hi => ?_⟩
  have := congrArg V.subtype (hu ⟨F i, hF i hi⟩ (Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_attach _ _, rfl⟩))
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using this

theorem spans_linear {I X Z : Type} (S : Finset I) (F : I → X → ℂ) (Tm : (X → ℂ) →ₗ[ℂ] (Z → ℂ)) (z : Z) (g : I → ℂ)
    (hg : ∀ i ∈ S, g i = Tm (F i) z) : Spans S (fun x i => F i x) g := by
  obtain ⟨P, u, -, hu⟩ := reproducing S ⊤ F fun _ _ => trivial
  refine ⟨X, P, fun x => Tm (u x) z, id, fun i hi => ?_⟩
  rw [hg i hi]
  conv_lhs => rw [hu i hi]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, id]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

def vacSp {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f ∧ IsLatVac (heisO ψ S T) Λ f}
  add_mem' := by
    intro f g hf hg
    have key : ∀ u, heisO ψ S T u (f + g) = heisO ψ S T u f + heisO ψ S T u g := fun u => by
      funext w; simp only [heisO, Pi.add_apply, mul_add]
    refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_add hf.1 hg.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [key, hf.2.1 u hu, hg.2.1 u hu]
    · rw [key, hf.2.2 e he u hu hh, hg.2.2 e he u hu hh]
  zero_mem' := ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T, fun u _ => by funext w; simp [heisO],
    fun e _ u _ _ => by funext w; simp [heisO]⟩
  smul_mem' := by
    intro c f hf
    have key : ∀ u, heisO ψ S T u (c • f) = c • heisO ψ S T u f := fun u => by
      funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
    refine ⟨GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hf.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [key, hf.2.1 u hu]
    · rw [key, hf.2.2 e he u hu hh]

theorem col_position {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {t : T} (j : ℕ)
    {I : Type} (S : Finset I) (e : AE D) (d₁ : I → FinDatum G t (.top t j)) (d₂ : I → FinDatum G t (.top t (j + 1)))
    (c₁ : I → (WO (G.V (.top j)) (G.V (.top (j + 1))) →₀ ℂ)) (c₂ : I → (WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) →₀ ℂ))
    (h₁ : ∀ i ∈ S, (d₁ i).e = e ∧ IsCombOf W (d₁ i) (c₁ i)) (h₂ : ∀ i ∈ S, (d₂ i).e = e ∧ IsCombOf W (d₂ i) (c₂ i))
    (C : WO (G.V (.top j)) (G.V (.top (j + 1))) → WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ)
    (hC : IsBiVac W.ψ _ _ _ (G.Λ (.top j) : Set _) (G.Λ (.top (j + 1)) : Set _) (G.Λ (.top (j + 1 + 1)) : Set _) C) (u v) :
    Spans S (fun (p : WO (G.V (.top j)) (G.V (.top (j + 1))) × WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))) i =>
      (d₁ i).fn p.1 * (d₂ i).fn p.2) fun i => biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v := by
  classical
  choose Tu hTu using fun u' => row_position W S e d₂ c₂ h₂ (C u') (hC.right u').1 (hC.right u').2
  let Lm : (WO (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) → ℂ) →ₗ[ℂ] (WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ) :=
    LinearMap.pi fun u' => (LinearMap.proj v) ∘ₗ Tu u'
  let Vac := vacSp W.ψ _ _ (latO (G.V (.top j)) (G.V (.top (j + 1))) (G.Λ (.top j) : Set _) (G.Λ (.top (j + 1)) : Set _) fun _ => True)
  have hL : ∀ i ∈ S, Lm (d₂ i).fn = fun u' => comb W.ψ _ _ (c₂ i) (C u') v := fun i hi => by
    funext u'
    exact (congrFun (hTu u' i hi) v).symm
  have hV : ∀ i ∈ S, (d₂ i).fn ∈ Vac.comap Lm := fun i hi => by
    rw [Submodule.mem_comap, hL i hi]
    have : (fun u' => comb W.ψ _ _ (c₂ i) (C u') v) =
        ∑ b ∈ (c₂ i).support, ((c₂ i) b * W.ψ (symplOH _ _ v b)) • fun u' => C u' (v + b) := by
      funext u'
      simp only [GlobalTheory.BiCombStable.comb_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this]
    exact Vac.sum_mem fun b _ => Vac.smul_mem _ (hC.left (v + b))
  obtain ⟨P, ε, hε, hP⟩ := reproducing S (Vac.comap Lm) (fun i => (d₂ i).fn) hV
  choose Tx hTx using fun x => row_position W S e d₁ c₁ h₁ (Lm (ε x)) (hε x).1 (hε x).2
  obtain ⟨Q, η, -, hQ⟩ := reproducing S ⊤ (fun i => (d₁ i).fn) fun _ _ => trivial
  refine ⟨_, Q ×ˢ P, fun p => Tx p.2 (η p.1) u, id, fun i hi => ?_⟩
  have e1 : biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v = GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (d₂ i).fn) u := by
    rw [hL i hi]; rfl
  have e2 : ∀ x, GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (ε x)) = ∑ q ∈ Q, (d₁ i).fn q • Tx x (η q) := fun x => by
    refine (hTx x i hi).trans ?_
    refine (congrArg (Tx x) (hQ i hi)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  have e3 : GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (d₂ i).fn) =
      ∑ x ∈ P, (d₂ i).fn x • GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm (ε x)) := by
    refine (congrArg (fun f => GlobalTheory.BiCombStable.combL W.ψ _ _ (c₁ i) (Lm f)) (hP i hi)).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  show biComb W.ψ _ _ _ (c₁ i) (c₂ i) C u v = _
  rw [e1, e3, Finset.sum_product_right, Finset.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [e2, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, id]
  ring

theorem prod_range_pairs (f : ℕ → ℂ) (n : ℕ) :
    ∏ j ∈ Finset.range (2 * n), f j = ∏ k ∈ Finset.range n, f (2 * k) * f (2 * k + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, mul_assoc]

theorem sum_evT_eq_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (ρ : RealMatch W)
    (t : T) (e : AE D) (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat G t) (c : I → Combs G)
    (hd : ∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf W ((d i).1 j) ((c i).1 j)) ∧
      ∀ n, ((d i).2 n).e = e ∧ IsCombOf W ((d i).2 n) ((c i).2 n))
    (h : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) (y : RowPt G), (∀ j, IsHalf e (u j)) →
      (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0)
    (C : BiFam G) (hC : IsRealFam W C) (u : ColPt G) (y : RowPt G) :
    ∑ i ∈ S, x i * evT (combC W (c i) C) (combR ρ (c i)) u y = 0 := by
  classical
  have hm : 0 + 2 * ((D.R.m - 2) / 2) + 2 = D.R.m := top_idx
  have h' : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))) (y : RowPt G),
      ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0 := by
    intro u y
    by_cases hu : ∀ j, IsHalf e (u j)
    · by_cases hy : ∀ n, IsHalf e (y n)
      · exact h u y hu hy
      · obtain ⟨n, hn⟩ := not_forall.1 hy
        refine Finset.sum_eq_zero fun i hi => ?_
        have h0 : ((d i).2 n).fn (y n) = 0 := by
          by_contra h0
          exact hn (((hd i hi).2 n).1 ▸ ((d i).2 n).sb.1 _ h0)
        rw [Finset.prod_eq_zero (f := fun n => ((d i).2 n).fn (y n)) (Finset.mem_univ n) h0, mul_zero, mul_zero]
    · obtain ⟨j, hj⟩ := not_forall.1 hu
      refine Finset.sum_eq_zero fun i hi => ?_
      have h0 : ((d i).1 j).fn (u j) = 0 := by
        by_contra h0
        exact hj (((hd i hi).1 j).1 ▸ ((d i).1 j).sb.1 _ h0)
      rw [Finset.prod_eq_zero (f := fun j => ((d i).1 j).fn (u j)) (Finset.mem_univ j) h0, zero_mul, mul_zero]

  have hrow : ∀ (u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1)))),
      ∑ i ∈ S, (x i * ∏ j, ((d i).1 j).fn (u j)) * ∏ n, combR ρ (c i) n (y n) = 0 := by
    intro u
    refine sum_prod_eq_zero S _ (fun (n : Fin D.R.m) (z : WO (G.pS (.chi n D.R.m : Pair T)) (G.pT (.chi n D.R.m : Pair T))) i =>
      ((d i).2 n).fn z) (fun n i => combR ρ (c i) n (y n)) (fun n => ?_) fun z => ?_
    · have hv := ρ.vX_is n D.R.m n.2 le_rfl
      obtain ⟨Tm, hTm⟩ := row_position W S e (fun i => (d i).2 n) (fun i => (c i).2 n) (fun i hi => (hd i hi).2 n) _
        hv.2.theta hv.2.lat
      exact spans_linear S (fun i => ((d i).2 n).fn) Tm (y n) _ fun i hi => congrFun (hTm i hi) (y n)
    · simpa only [mul_assoc] using h' u z

  let F : I → ∀ j : ℕ, WO (G.V (.top j)) (G.V (.top (j + 1))) → ℂ := fun i j =>
    if hj : j < D.R.m then ((d i).1 ⟨j, hj⟩).fn else 0
  have hcol := sum_prod_eq_zero (ι := Fin (D.R.m / 2)) S (fun i => x i * ∏ n, combR ρ (c i) n (y n))
    (fun k (w : ColPt G) i => F i (2 * k) (w (2 * k)) * F i (2 * k + 1) (w (2 * k + 1)))
    (fun k i => combC W (c i) C (2 * k) (u (2 * k)) (u (2 * k + 1))) (fun k => ?_) fun z => ?_
  · rw [← hcol]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [evT, Finset.prod_range]
    ring
  · have k0 : 2 * (k : ℕ) < D.R.m := by have := k.2; omega
    have k1 : 2 * (k : ℕ) + 1 < D.R.m := by have := k.2; omega
    obtain ⟨J, P, a, p, hp⟩ := col_position W (2 * k) S e (fun i => (d i).1 ⟨2 * k, k0⟩) (fun i => (d i).1 ⟨2 * k + 1, k1⟩)
      (fun i => (c i).1 (2 * k)) (fun i => (c i).1 (2 * k + 1)) (fun i hi => (hd i hi).1 ⟨2 * k, k0⟩)
      (fun i hi => (hd i hi).1 ⟨2 * k + 1, k1⟩) (C (2 * k)) (hC _ (even_two_mul _) k0).1 (u (2 * k)) (u (2 * k + 1))
    refine ⟨J, P, a, fun j => Function.update (Function.update (0 : ColPt G) (2 * k) (p j).1) (2 * k + 1) (p j).2,
      fun i hi => (hp i hi).trans (Finset.sum_congr rfl fun j _ => ?_)⟩
    simp only [F, dif_pos k0, dif_pos k1, Function.update_self,
      Function.update_of_ne (show 2 * (k : ℕ) ≠ 2 * k + 1 by omega)]
  · let w : ColPt G := fun j => if hj : j / 2 < D.R.m / 2 then z ⟨j / 2, hj⟩ j else 0
    have hw : ∀ (k : Fin (D.R.m / 2)) (j : ℕ), j / 2 = (k : ℕ) → w j = z k j := by
      rintro ⟨k, hk⟩ j hj
      have hj' : j / 2 = k := hj
      subst hj'
      exact dif_pos hk
    rw [← hrow fun j => w j]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : ∏ j : Fin D.R.m, ((d i).1 j).fn (w j) = ∏ j ∈ Finset.range D.R.m, F i j (w j) := by
      rw [Finset.prod_range]
      exact Finset.prod_congr rfl fun j _ => by simp only [F, dif_pos j.2]
    have e2 : Finset.range D.R.m = Finset.range (2 * (D.R.m / 2)) := by congr 1; omega
    rw [e1, e2, prod_range_pairs (fun j => F i j (w j)), Finset.prod_range,
      Finset.prod_congr rfl fun (k : Fin (D.R.m / 2)) _ => show F i (2 * k) (w (2 * k)) * F i (2 * k + 1) (w (2 * k + 1)) =
        F i (2 * k) (z k (2 * k)) * F i (2 * k + 1) (z k (2 * k + 1)) by
          rw [hw k _ (by omega), hw k _ (by omega)]]
    ring

theorem comb_det : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t e, IsIdemSum e (locPl ch.G t) → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat ch.G t) (c : I → Combs ch.G), (∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf ch.W ((d i).1 j) ((c i).1 j)) ∧ ∀ n, ((d i).2 n).e = e ∧ IsCombOf ch.W ((d i).2 n) ((c i).2 n)) → (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : RowPt ch.G), (∀ j, IsHalf e (u j)) → (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0) → ∀ C, IsRealFam ch.W C → ∀ u y, ∑ i ∈ S, x i * evT (combC ch.W (c i) C) (combR ch.rm (c i)) u y = 0 :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t e _ I S x d c hd h C hC u y =>
    sum_evT_eq_zero ch.W ch.rm t e I S x d c hd h C hC u y⟩⟩

end GlobalTheory.CombDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestCombinationDependsOnProductFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_combination_depends_on_product_function : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t e, IsIdemSum e (locPl ch.G t) → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (d : I → PureDat ch.G t) (c : I → Combs ch.G), (∀ i ∈ S, (∀ j : Fin D.R.m, ((d i).1 j).e = e ∧ IsCombOf ch.W ((d i).1 j) ((c i).1 j)) ∧ ∀ n, ((d i).2 n).e = e ∧ IsCombOf ch.W ((d i).2 n) ((c i).2 n)) → (∀ (u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) (y : RowPt ch.G), (∀ j, IsHalf e (u j)) → (∀ n, IsHalf e (y n)) → ∑ i ∈ S, x i * ((∏ j, ((d i).1 j).fn (u j)) * ∏ n, ((d i).2 n).fn (y n)) = 0) → ∀ C, IsRealFam ch.W C → ∀ u y, ∑ i ∈ S, x i * evT (combC ch.W (c i) C) (combR ch.rm (c i)) u y = 0 := by
  first | exact @GlobalTheory.CombDet.comb_det | exact GlobalTheory.CombDet.comb_det | (intros; apply GlobalTheory.CombDet.comb_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryRelativeBaseVacuaLargeDepth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal

namespace GlobalTheory.LocAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw


set_option maxHeartbeats 1600000 in
open Classical in
theorem locAt_of_placeAt : Big fun ch => ∀ s, PlaceAt ch s → ConLin ch → LocAt ch s := by
  refine big_mono ?_ (Big.and GlobalTheory.T.flippedFiniteTensor_sum_prod_local_pure_tensors (Big.and GlobalTheory.T.localPureTensor_product_expansion_all_places (Big.and GlobalTheory.T.unfoldedVacuaAreRealDatum_largeDepth GlobalTheory.T.rowTest_combination_depends_on_product_function)))
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s hP hcon
  obtain ⟨hR, hS, hV, hC⟩ := h
  obtain ⟨κ, z, hz, hκ, hPl⟩ := (placeAt_iff ch s).1 hP
  refine ⟨∏ w ∈ ch.G.pl.W0, κ w, fun t => ∏ w ∈ locPl ch.G t, z t w, fun t => Subgroup.prod_mem _ fun w _ => hz t w, ?_⟩
  intro t Φ τ hτ M hM β b b₀ hb hb₀ τ' c hτ' hc
  have hζ : ∀ w : locPl ch.G t, ∃ ζ : ℂ, ((w.1 ∈ ch.G.pl.W0 → ∀ i, β w i = DoubleCoset.mk _ _
      (stair (locGrid ch.G t w.1) (unifAt w.1) (cosExp ch.G w.1) (i + 1))) → ζ = κ w.1 * (z t w.1 : ℂ)⁻¹) ∧
      PlaceCl ch s t w.1 (β w) ζ := fun w => hPl t w.1 w.2 (β w)
  choose ζ hζ1 hζ2 using hζ
  refine ⟨∏ w, ζ w, fun hst => ?_, ?_⟩
  · have e1 : ∀ w : locPl ch.G t, ζ w = κ w.1 * (z t w.1 : ℂ)⁻¹ := fun w => hζ1 w (hst w)
    rw [Finset.prod_congr rfl fun w _ => e1 w, Finset.prod_mul_distrib]
    congr 1
    · rw [Finset.prod_coe_sort (locPl ch.G t) κ]
      exact (Finset.prod_subset Finset.subset_union_left fun w _ hw => hκ w hw).symm
    · rw [Finset.prod_coe_sort (locPl ch.G t) (fun w => ((z t w : ℂ))⁻¹), Units.coe_prod, Finset.prod_inv_distrib]
  · intro P p hp u y
    obtain ⟨e, he, hτe, hτ'p⟩ := hτ'
    obtain ⟨α, SA, xA, φ, fd, fr, hnat, hvec, hflat, hlhs⟩ := hR hcon t Φ τ hτ β e he
    have hS' : ∀ a ∈ SA, ∃ σ : (PureDat ch.G t × Combs ch.G) →₀ ℂ, _ := fun a ha =>
      hS s t β ζ hζ2 M hM b b₀ hb hb₀ e he (φ a) (hnat a ha) (fd a) (fr a) (hvec a ha).1 (hvec a ha).2
    choose! σ hσ1 hσ2 hσ3 using hS'
    set C₀ := conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀) with hC₀
    set μ : (PureDat ch.G t × Combs ch.G) →₀ ℂ := τ'.mapDomain (fun d => (d, c d)) - ∑ a ∈ SA, xA a • σ a with hμ
    have hL : ∀ G : PureDat ch.G t × Combs ch.G → ℂ, ∑ i ∈ μ.support, μ i * G i =
        (τ'.sum fun d x => x * G (d, c d)) - ∑ a ∈ SA, xA a * (σ a).sum fun k x => x * G k := fun G => by
      have e1 : ∀ {ι : Type} (G' : ι → ℂ) (ν : ι →₀ ℂ), Finsupp.linearCombination ℂ G' ν = ν.sum fun k x => x * G' k :=
        fun G' ν => by rw [Finsupp.linearCombination_apply]; rfl
      have e2 : ∑ i ∈ μ.support, μ i * G i = Finsupp.linearCombination ℂ G μ := by rw [e1]; rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e2, hμ, map_sub, map_sum, Finsupp.linearCombination_mapDomain, e1]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, e1, smul_eq_mul]
    have hsupp : ∀ i ∈ μ.support, (∀ j : Fin D.R.m, (i.1.1 j).e = e ∧ IsCombOf ch.W (i.1.1 j) (i.2.1 j)) ∧
        ∀ n, (i.1.2 n).e = e ∧ IsCombOf ch.W (i.1.2 n) (i.2.2 n) := by
      intro i hi
      rcases Finset.mem_union.1 (Finsupp.support_sub hi) with h1 | h2
      · obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h1)
        exact ⟨fun j => ⟨((hτe d hd).1 j).2.1, (hc d hd).1 j⟩, fun n => ⟨((hτe d hd).2 n).2.1, (hc d hd).2 n⟩⟩
      · have hex : ∃ a ∈ SA, i ∈ (xA a • σ a).support := by
          by_contra hn
          push_neg at hn
          have hz : (∑ a ∈ SA, xA a • σ a) i = 0 := by
            simp only [Finset.sum_apply']
            apply Finset.sum_eq_zero
            intro a ha
            exact Finsupp.notMem_support_iff.mp (hn a ha)
          exact (Finsupp.mem_support_iff.mp h2) hz
        obtain ⟨a, ha, hi'⟩ := hex
        exact hσ1 a ha i (Finsupp.support_smul hi')
    have hzero := hC t e he (PureDat ch.G t × Combs ch.G) μ.support μ Prod.fst Prod.snd hsupp (fun u' y' hu hy => by
      rw [hL]
      have h1 := hτ'p u' y' hu hy
      have h2 := hflat u' y' hu hy
      rw [sub_eq_zero, Finset.sum_congr rfl fun a ha => by rw [hσ2 a ha u' y' hu hy], ← h2, ← h1]
      refine Finsupp.sum_congr fun d _ => ?_
      ring) C₀ (hV t M hM b₀ hb₀ P p hp) u y
    rw [hL, sub_eq_zero] at hzero
    rw [hlhs M hM P (p * b) u y, Finset.sum_congr rfl fun a ha => by rw [hσ3 a ha P p hp u y], hzero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

end GlobalTheory.LocAsm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryRelativeBaseVacuaLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_dictionary_relative_base_vacua_large_depth : Big fun ch => ∀ s, PlaceAt ch s → ConLin ch → LocAt ch s := by
  first | exact @GlobalTheory.LocAsm.locAt_of_placeAt | exact GlobalTheory.LocAsm.locAt_of_placeAt | (intros; apply GlobalTheory.LocAsm.locAt_of_placeAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryBaseVacuaLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem exists_locAt_big : Big fun ch => ∃ s, LocAt ch s :=
  GlobalTheory.RowReal.big_mono (fun ch h => by
               obtain ⟨⟨⟨s, hP⟩, hC⟩, hL⟩ := h
               exact ⟨s, hL s hP hC⟩)
    (Big.and (Big.and GlobalTheory.T.exists_sign_flatDictionaryAtOnePlace_largeDepth GlobalTheory.T.unfoldedProduct_depends_on_dataProduct) GlobalTheory.T.flat_dictionary_relative_base_vacua_large_depth)

end GlobalTheory.RowVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryBaseVacuaLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_dictionary_base_vacua_large_depth : Big fun ch => ∃ s, LocAt ch s := by
  first | exact @GlobalTheory.RowVal.exists_locAt_big | exact GlobalTheory.RowVal.exists_locAt_big | (intros; apply GlobalTheory.RowVal.exists_locAt_big <;> assumption)
end
