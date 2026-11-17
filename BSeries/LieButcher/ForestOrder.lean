import HopfAlgebras.Trees.Planar

/-! # Order bounds for sub-forests of an ordered forest -/

namespace HopfAlgebras.PTree

theorem order_le_orderList_of_mem {ts : List PTree} {t : PTree} (ht : t ∈ ts) :
    order t ≤ orderList ts := by
  induction ts with
  | nil => simp at ht
  | cons u us ih =>
      rcases List.mem_cons.mp ht with rfl | h
      · exact Nat.le_add_right _ _
      · exact (ih h).trans (Nat.le_add_left _ _)

theorem orderList_take_le (ts : List PTree) (j : ℕ) :
    orderList (ts.take j) ≤ orderList ts := by
  have := orderList_append (ts.take j) (ts.drop j)
  rw [List.take_append_drop] at this
  omega

theorem orderList_drop_le (ts : List PTree) (j : ℕ) :
    orderList (ts.drop j) ≤ orderList ts := by
  have := orderList_append (ts.take j) (ts.drop j)
  rw [List.take_append_drop] at this
  omega

/-- A child has smaller order than its parent. -/
theorem order_lt_of_mem_children {ts : List PTree} {t : PTree} (ht : t ∈ ts) :
    order t < order (.node ts) := by
  have := order_le_orderList_of_mem ht
  have := order_eq_one_add_orderList_children (.node ts)
  simp only [children] at this
  omega

end HopfAlgebras.PTree
