use crate::rule_book::{RuleLhs, RuleRhs};
use hashbrown::HashMap;
// use derive_new::new;
// use vec_map::VecMap;

pub type RuleMap = HashMap<RuleLhs, RuleRhs>;
/*
/// Uses integer keys in the form `lhs_id * agent_count + rhs_id` to map from RuleLhs to RuleRhs
#[derive(new, Clone)]
pub struct RuleMap {
  agent_count: usize,
  #[new(default)]
  map: VecMap<RuleRhs>,
}

impl RuleMap {
  #[inline(always)]
  fn map_key(&self, (lhs_id, rhs_id): RuleLhs) -> usize {
    lhs_id * self.agent_count + rhs_id
  }

  pub fn insert(&mut self, key: RuleLhs, value: RuleRhs) -> Option<RuleRhs> {
    self.map.insert(self.map_key(key), value)
  }

  pub fn get(&self, key: &RuleLhs) -> Option<&RuleRhs> {
    self.map.get(self.map_key(*key))
  }
}
*/
