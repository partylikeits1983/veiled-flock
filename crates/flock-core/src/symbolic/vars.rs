use std::collections::BTreeMap;

/// Closed registry of transcript challenges used by symbolic artifacts.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Var {
    Z,
    Gamma,
    Rho(u8),
    ROuter(u8),
    GammaLc,
    Alpha(u8),
    Beta(u8),
    C,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct VarSet {
    vars: Vec<Var>,
    indices: BTreeMap<Var, usize>,
}

impl VarSet {
    pub fn new(vars: impl IntoIterator<Item = Var>) -> Self {
        let mut out = Self::default();
        for var in vars {
            out.insert(var);
        }
        out
    }

    pub fn insert(&mut self, var: Var) -> usize {
        if let Some(index) = self.indices.get(&var) {
            return *index;
        }
        let index = self.vars.len();
        self.vars.push(var.clone());
        self.indices.insert(var, index);
        index
    }

    pub fn index(&self, var: &Var) -> Option<usize> {
        self.indices.get(var).copied()
    }

    pub fn vars(&self) -> &[Var] {
        &self.vars
    }

    pub fn len(&self) -> usize {
        self.vars.len()
    }

    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }
}
