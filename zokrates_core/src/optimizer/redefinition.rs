//! Module containing the `RedefinitionOptimizer` to remove code of the form
// ```
// b := a
// c := b
// ```
// and replace by
// ```
// c := a
// ```

use flat_absy::flat_variable::FlatVariable;
use ir::folder::fold_variable;
use ir::folder::{fold_statement, Folder};
use ir::LinComb;
use ir::*;
use num::Zero;
use std::collections::HashMap;
use zokrates_field::field::Field;

pub struct RedefinitionOptimizer<T: Field> {
    /// Map of renamings for reassigned variables while processing the program.
    substitution: HashMap<FlatVariable, LinComb<T>>,
    /// Index of the next introduced variable while processing the program.
    next_var_idx: Counter,
}

impl<T: Field> RedefinitionOptimizer<T> {
    fn new() -> RedefinitionOptimizer<T> {
        RedefinitionOptimizer {
            substitution: HashMap::new(),
            next_var_idx: Counter { value: 0 },
        }
    }

    pub fn optimize(p: Prog<T>) -> Prog<T> {
        RedefinitionOptimizer::new().fold_program(p)
    }
}

pub struct Counter {
    value: usize,
}

impl Counter {
    fn increment(&mut self) -> usize {
        let index = self.value;
        self.value = self.value + 1;
        index
    }
}

impl<T: Field> Folder<T> for RedefinitionOptimizer<T> {
    fn fold_statement(&mut self, s: Statement<T>) -> Vec<Statement<T>> {
        // generate substitution map
        //
        //  (b = a, c = b) => ( b -> a, c -> a )
        // The first variable to appear is used for its synonyms.
        match s {
            // Detect constraints of the form `lincomb * ~ONE == x` where x is not in the map yet
            Statement::Constraint(quad, lin) => {
                let quad = self.fold_quadratic_combination(quad);
                let lin = self.fold_linear_combination(lin);

                let to_insert = match quad.try_linear() {
                    // left side must be linear
                    Some(l) => match lin.try_summand() {
                        // right side must be a single variable
                        Some((variable, coefficient)) => {
                            match variable.is_public() || variable == &FlatVariable::one() {
                                // variable must not be public nor ~ONE
                                false => match self.substitution.get(variable) {
                                    Some(_) => None,
                                    None => Some((*variable, l / &coefficient)),
                                },
                                true => None,
                            }
                        }
                        None => None,
                    },
                    None => None,
                };

                match to_insert {
                    Some((k, v)) => {
                        self.substitution.insert(k, v);
                        vec![]
                    }
                    None => vec![Statement::Constraint(quad, lin)],
                }
            }
            Statement::Directive(d) => {
                for o in d.outputs.iter() {
                    self.substitution.insert(
                        o.clone(),
                        FlatVariable::new(self.next_var_idx.increment()).into(),
                    );
                }
                fold_statement(self, Statement::Directive(d))
            }
        }
    }

    fn fold_argument(&mut self, a: FlatVariable) -> FlatVariable {
        // each parameter is a new variable
        let optimized_variable = FlatVariable::new(self.next_var_idx.increment());
        self.substitution.insert(a, optimized_variable.into());
        fold_variable::<T, _>(self, a)
    }

    fn fold_linear_combination(&mut self, lc: LinComb<T>) -> LinComb<T> {
        // for each summand, check if it is equal to a linear term in our substitution, otherwise keep it as is
        lc.0.into_iter()
            .map(
                |(variable, coefficient)| match self.substitution.get(&variable) {
                    Some(l) => l.clone() * &coefficient, // we only clone in the case that we found a value in the map
                    None => LinComb::summand(coefficient, variable),
                },
            )
            .fold(LinComb::zero(), |acc, x| acc + x)
    }

    fn fold_function(&mut self, funct: Function<T>) -> Function<T> {
        let optimized_arguments = funct
            .arguments
            .into_iter()
            .map(|a| <RedefinitionOptimizer<T> as Folder<T>>::fold_argument(self, a))
            .collect();
        let optimized_statements: Vec<_> = funct
            .statements
            .into_iter()
            .flat_map(|s| self.fold_statement(s))
            .collect();
        let optimized_returns = funct
            .returns
            .into_iter()
            .map(|q| <RedefinitionOptimizer<T> as Folder<T>>::fold_quadratic_combination(self, q))
            .collect();

        Function {
            arguments: optimized_arguments,
            statements: optimized_statements,
            returns: optimized_returns,
            ..funct
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use zokrates_field::field::FieldPrime;

    #[test]
    fn remove_synonyms() {
        // def main(x):
        //    y = x
        //    z = y
        //    return z

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![Statement::definition(y, x), Statement::definition(z, y)],
            returns: vec![z.into()],
        };

        let optimized: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![],
            returns: vec![x.into()],
        };

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn remove_synonyms_in_condition() {
        // def main(x) -> (1):
        //    y = x
        //    z = y
        //    z == y
        //    return z

        // ->

        // def main(x) -> (1)
        //    x == x // will be eliminated as a tautology
        //    return x

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(y, x),
                Statement::definition(z, y),
                Statement::constraint(z, y),
            ],
            returns: vec![z.into()],
        };

        let optimized: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![Statement::constraint(x, x)],
            returns: vec![x.into()],
        };

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn remove_multiple_synonyms() {
        // def main(x) -> (2):
        //    y = x
        //    t = 1
        //    z = y
        //    w = t
        //    return z, w

        // ->

        // def main(x):
        //. return x, 1

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let z = FlatVariable::new(2);
        let t = FlatVariable::new(3);
        let w = FlatVariable::new(4);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::definition(y, x),
                Statement::definition(t, FieldPrime::from(1)),
                Statement::definition(z, y),
                Statement::definition(w, t),
            ],
            returns: vec![z.into(), w.into()],
        };

        let optimized: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![],
            returns: vec![x.into(), FieldPrime::from(1).into()],
        };

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn substitute_lincomb() {
        // def main(x, y) -> (1):
        //     a = x + y
        //     b = a + x + y
        //     c = b + x + y
        //     2*c == 6*x + 6*y
        //     return a + b + c

        // ->

        // def main(x, y) -> (1):
        //    6*x + 6*y == 6*x + 6*y // will be eliminated as a tautology
        //    return 6*x + 6*y

        let x = FlatVariable::new(0);
        let y = FlatVariable::new(1);
        let a = FlatVariable::new(2);
        let b = FlatVariable::new(3);
        let c = FlatVariable::new(4);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x, y],
            statements: vec![
                Statement::definition(a, LinComb::from(x) + LinComb::from(y)),
                Statement::definition(b, LinComb::from(a) + LinComb::from(x) + LinComb::from(y)),
                Statement::definition(c, LinComb::from(b) + LinComb::from(x) + LinComb::from(y)),
                Statement::constraint(
                    LinComb::summand(2, c),
                    LinComb::summand(6, x) + LinComb::summand(6, y),
                ),
            ],
            returns: vec![(LinComb::from(a) + LinComb::from(b) + LinComb::from(c)).into()],
        };

        let optimized: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x, y],
            statements: vec![Statement::constraint(
                LinComb::summand(6, x) + LinComb::summand(6, y),
                LinComb::summand(6, x) + LinComb::summand(6, y),
            )],
            returns: vec![(LinComb::summand(6, x) + LinComb::summand(6, y)).into()],
        };

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }

    #[test]
    fn keep_existing_variable() {
        // def main(x) -> (1):
        //     x == 1
        //     x == 2
        //     return x

        // ->

        // unchanged

        let x = FlatVariable::new(0);

        let f: Function<FieldPrime> = Function {
            id: "foo".to_string(),
            arguments: vec![x],
            statements: vec![
                Statement::constraint(x, FieldPrime::from(1)),
                Statement::constraint(x, FieldPrime::from(2)),
            ],
            returns: vec![x.into()],
        };

        let optimized = f.clone();

        let mut optimizer = RedefinitionOptimizer::new();
        assert_eq!(optimizer.fold_function(f), optimized);
    }
}