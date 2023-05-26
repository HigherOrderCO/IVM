use crate::rule_book::{RuleLhs, RuleRhs};
use hashbrown::HashMap;

pub type RuleMap = HashMap<RuleLhs, RuleRhs>;

/*
use derive_new::new;
use num_integer::div_rem;
use vec_map::VecMap;

/// Uses integer keys in the form `lhs_id * agent_count + rhs_id` to map from RuleLhs to RuleRhs
#[derive(new, Clone)]
pub struct RuleMap {
  pub(super) agent_count: usize,
  #[new(default)]
  map: VecMap<RuleRhs>,
}

impl RuleMap {
  #[inline(always)]
  fn map_key(agent_count: usize, (lhs_id, rhs_id): RuleLhs) -> usize {
    lhs_id * agent_count + rhs_id
  }

  #[inline(always)]
  fn unmap_key(agent_count: usize, key: usize) -> RuleLhs {
    div_rem(key, agent_count)
  }

  pub fn insert(&mut self, key: RuleLhs, value: RuleRhs) -> Option<RuleRhs> {
    self.map.insert(Self::map_key(self.agent_count, key), value)
  }

  #[inline(always)]
  pub fn get(&self, key: &RuleLhs) -> Option<&RuleRhs> {
    self.map.get(Self::map_key(self.agent_count, *key))
  }

  pub fn into_iter(self) -> impl Iterator<Item = (RuleLhs, RuleRhs)> {
    self.map.into_iter().map(move |(key, value)| (Self::unmap_key(self.agent_count, key), value))
  }

  pub fn iter(&self) -> impl Iterator<Item = (RuleLhs, &RuleRhs)> {
    self.map.iter().map(move |(key, value)| (Self::unmap_key(self.agent_count, key), value))
  }

  pub fn keys(&self) -> impl Iterator<Item = RuleLhs> + '_ {
    self.map.keys().map(|key| Self::unmap_key(self.agent_count, key))
  }

  pub fn contains_key(&self, key: &RuleLhs) -> bool {
    self.map.contains_key(Self::map_key(self.agent_count, *key))
  }

  pub fn from_iter<I: IntoIterator<Item = (RuleLhs, RuleRhs)>>(agent_count: usize, iter: I) -> Self {
    let mut r = Self::new(agent_count);
    r.map.extend(iter.into_iter().map(|(key, value)| (Self::map_key(agent_count, key), value)));
    r
  }

  pub fn extend<T: IntoIterator<Item = (RuleLhs, RuleRhs)>>(&mut self, iter: T) {
    self.map.extend(iter.into_iter().map(|(key, value)| (Self::map_key(self.agent_count, key), value)));
  }
}
*/
