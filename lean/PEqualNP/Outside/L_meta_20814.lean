import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_20814.Helpers

theorem weight (S : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (k : ℕ) :
    (∑ x ∈ S, if P x then k else 0) = k * (S.filter P).card := by
  rw [← Finset.sum_filter]
  simp [Nat.mul_comm]

theorem input_bound (S : Finset ℕ) (R : ℕ → ℕ) :
    (∑ w ∈ S.filter (fun w => 2 ≤ R w), R w) +
      2 * (S.filter (fun w => 1 ≤ R w)).card ≤ 2 * ∑ w ∈ S, R w := by
  classical
  calc
    _ = ∑ w ∈ S, ((if 2 ≤ R w then R w else 0) + (if 1 ≤ R w then 2 else 0)) := by
      rw [Finset.sum_add_distrib, weight, Finset.sum_filter]
    _ ≤ ∑ w ∈ S, 2 * R w := by
      apply Finset.sum_le_sum
      intro w hw
      split_ifs <;> omega
    _ = _ := by rw [Finset.mul_sum]

theorem gate_bound (S : Finset ℕ) (R : ℕ → ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ j ∈ S.filter (fun j => Q j ∨ 2 ≤ R j), R j) ≤
      2 * (∑ j ∈ S, (R j - 1)) + 2 * (S.filter Q).card := by
  classical
  calc
    _ = ∑ j ∈ S, if Q j ∨ 2 ≤ R j then R j else 0 := by rw [Finset.sum_filter]
    _ ≤ ∑ j ∈ S, (2 * (R j - 1) + (if Q j then 2 else 0)) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases h : Q j <;> by_cases h' : 2 ≤ R j <;> simp only [h,h',or_true,or_false,if_true,if_false] <;> omega
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, weight]

noncomputable def filt (P : ℕ → Prop) (S : Finset ℕ) : Finset ℕ :=
  @Finset.filter ℕ P (fun _ => Classical.propDecidable _) S

end PEqualNP.Outside.L_meta_20814.Helpers

theorem PEqualNP.Outside.L_meta_20814 : ∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
  (∑ w ∈ @Finset.filter ℕ
        (fun w1 => 2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w1)
        (fun d1 => Classical.propDecidable _) (Finset.range m),
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
    (∑ j ∈ @Finset.filter ℕ
        (fun j1 => (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).op =
            PEqualNP.CircuitLowerBounds.GateOp.not ∨
          2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j1))
        (fun d2 => Classical.propDecidable _) (Finset.range C.size),
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) +
    2 * (@Finset.filter ℕ
        (fun w2 => 1 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w2)
        (fun d3 => Classical.propDecidable _) (Finset.range m)).card ≤
  2 * ((∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d4 => Classical.propDecidable _)
          (Finset.range C.size),
        (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1)) +
      (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d5 => Classical.propDecidable _)
          (Finset.range C.size)).card) := by
  intro m C shape back positive last
  classical
  try simp only [Finset.filter_congr_decidable] at *
  let R := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  have hi := PEqualNP.Outside.L_meta_20814.Helpers.input_bound (Finset.range m) R
  have hg := PEqualNP.Outside.L_meta_20814.Helpers.gate_bound (Finset.range C.size)
    (fun j => R (m+j)) (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.not)
  have excess : (∑ j ∈ Finset.range C.size, (R (m+j)-1)) =
      ∑ j ∈ (Finset.range C.size).filter (fun j => j+1<C.size), (R (m+j)-1) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j hj hn
    have lt : j < C.size := Finset.mem_range.mp hj
    have endeq : j+1=C.size := by
      have : ¬j+1<C.size := by
        intro h
        exact hn (Finset.mem_filter.mpr ⟨hj,h⟩)
      omega
    have zero := (last j lt).mpr endeq
    change R (m+j)=0 at zero
    simp [zero]
  rw [excess] at hg
  let filt := PEqualNP.Outside.L_meta_20814.Helpers.filt
  have hiC : (∑ w ∈ filt (fun w => 2 ≤ R w) (Finset.range m), R w) +
      2 * (filt (fun w => 1 ≤ R w) (Finset.range m)).card ≤
      2 * (∑ w ∈ Finset.range m, R w) := by
    convert hi using 1 <;> dsimp only [filt, PEqualNP.Outside.L_meta_20814.Helpers.filt] <;> congr
  have hgC : (∑ j ∈ filt (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∨ 2 ≤ R (m+j)) (Finset.range C.size), R (m+j)) ≤
      2 * (∑ j ∈ filt (fun j => j+1<C.size) (Finset.range C.size), (R (m+j)-1)) +
      2 * (filt (fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.not) (Finset.range C.size)).card := by
    convert hg using 1 <;> dsimp only [filt, PEqualNP.Outside.L_meta_20814.Helpers.filt] <;> congr
  dsimp only [filt, PEqualNP.Outside.L_meta_20814.Helpers.filt, R] at hiC hgC
  clear hi hg excess
  omega
