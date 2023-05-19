/// Given a tuple of two elements of the same type, return a tuple with the elements sorted
#[inline(always)]
pub fn sort_tuple<T: PartialOrd>((lhs, rhs): (T, T)) -> (T, T) {
  if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) }
}

/// Given two tuples, return the tuples sorted by their first elements
#[inline(always)]
pub fn sort_tuples_by_fst<K: PartialOrd, V>(
  ((lhs_key, lhs_val), (rhs_key, rhs_val)): ((K, V), (K, V)),
) -> ((K, V), (K, V)) {
  if lhs_key <= rhs_key {
    ((lhs_key, lhs_val), (rhs_key, rhs_val))
  } else {
    ((rhs_key, rhs_val), (lhs_key, lhs_val))
  }
}
