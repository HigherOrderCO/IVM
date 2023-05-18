pub fn sort_tuple<T: PartialOrd>((lhs, rhs): (T, T)) -> (T, T) {
  if lhs <= rhs { (lhs, rhs) } else { (rhs, lhs) }
}

pub fn sort_tuples_by_fst<K: PartialOrd, V>(
  ((lhs_key, lhs_val), (rhs_key, rhs_val)): ((K, V), (K, V)),
) -> ((K, V), (K, V)) {
  if lhs_key <= rhs_key {
    ((lhs_key, lhs_val), (rhs_key, rhs_val))
  } else {
    ((rhs_key, rhs_val), (lhs_key, lhs_val))
  }
}
