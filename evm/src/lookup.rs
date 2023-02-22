use std::cmp::Ordering;

use itertools::Itertools;
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::hash::hash_types::RichField;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::config::GenericConfig;
use plonky2_util::ceil_div_usize;

use crate::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::stark::Stark;
use crate::vars::{StarkEvaluationTargets, StarkEvaluationVars};

pub struct Lookup {
    columns: Vec<usize>,
    table_column: usize,
    frequencies_column: usize,
}

/// Compute the helper columns for the lookup argument.
/// Given columns `f0,...,fk` and a column `t`, such that `∪fi ⊆ t`, and challenges `x`,
/// we compute the helper columns `h_i = 1/(x+f_2i) + 1/(x+f_2i+1)` and `g = 1/(x+t)`.
pub(crate) fn lookup_helper_columns<F: Field>(
    lookup: &Lookup,
    trace_poly_values: &[PolynomialValues<F>],
    challenge: F,
    degree: usize,
) -> Vec<PolynomialValues<F>> {
    let num_helper_columns = ceil_div_usize(lookup.columns.len(), degree - 1) + 2;
    let mut helper_columns: Vec<PolynomialValues<F>> = Vec::with_capacity(num_helper_columns);

    // TODO: This does one batch inversion per column. It would also be possible to do one batch inversion
    // for every column, but that would require building a big vector of all the columns concatenated.
    // Not sure which approach is better.
    // TODO: The clone could probably be avoided by using a modified version of `batch_multiplicative_inverse`
    // taking `challenge` as an additional argument.
    for mut col_inds in &lookup.columns.iter().chunks(degree - 1) {
        let first = *col_inds.next().unwrap();
        let mut column = trace_poly_values[first].values.clone();
        for x in column.iter_mut() {
            *x = challenge + *x;
        }
        let mut acc = F::batch_multiplicative_inverse(&column);
        for &ind in col_inds {
            let mut column = trace_poly_values[ind].values.clone();
            for x in column.iter_mut() {
                *x = challenge + *x;
            }
            column = F::batch_multiplicative_inverse(&column);
            for (x, y) in acc.iter_mut().zip(column) {
                *x += y;
            }
        }
        helper_columns.push(acc.into());
    }

    let mut table = trace_poly_values[lookup.table_column].values.clone();
    for x in table.iter_mut() {
        *x = challenge + *x;
    }
    helper_columns.push(F::batch_multiplicative_inverse(&table).into());

    let frequencies = &trace_poly_values[lookup.frequencies_column].values;
    let mut z = Vec::with_capacity(frequencies.len());
    z.push(F::ZERO);
    for i in 0..frequencies.len() - 1 {
        let x = helper_columns[..num_helper_columns - 2]
            .iter()
            .map(|col| col.values[i])
            .sum::<F>()
            - frequencies[i] * helper_columns[num_helper_columns - 2].values[i];
        z.push(z[i] + x);
    }
    helper_columns.push(z.into());

    // Constraints
    for i in 0..frequencies.len() {
        for j in 0..num_helper_columns - 2 {
            let mut x = helper_columns[j].values[i];
            let mut y = F::ZERO;
            let fs: Vec<_> = ((degree - 1) * j..(degree - 1) * (j + 1))
                .map(|k| trace_poly_values[lookup.columns[k]].values[i])
                .collect();
            for &f in &fs {
                x *= challenge + f;
                y += challenge + f;
            }
            assert_eq!(x, y);
        }
        let x = helper_columns[num_helper_columns - 2].values[i];
        let x = x * (challenge + trace_poly_values[lookup.table_column].values[i]);
        assert!(x.is_one());

        let z = helper_columns[num_helper_columns - 1].values[i];
        let next_z = helper_columns[num_helper_columns - 1].values[(i + 1) % frequencies.len()];
        let y = helper_columns[..num_helper_columns - 2]
            .iter()
            .map(|col| col.values[i])
            .sum::<F>()
            - trace_poly_values[lookup.table_column].values[i]
                * helper_columns[num_helper_columns - 2].values[i];
        assert_eq!(next_z - z, y);
    }

    helper_columns
}

pub struct LookupCheckVars<F, FE, P, const D2: usize>
where
    F: Field,
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
{
    pub(crate) local_values: Vec<P>,
    pub(crate) next_values: Vec<P>,
    // pub(crate) permutation_challenge_sets: Vec<GrandProductChallengeSet<F>>,
}

pub(crate) fn eval_lookups<F, FE, P, C, S, const D: usize, const D2: usize>(
    stark: &S,
    vars: StarkEvaluationVars<FE, P, { S::COLUMNS }>,
    lookup_vars: LookupCheckVars<F, FE, P, D2>,
    yield_constr: &mut ConstraintConsumer<P>,
    challenge: FE,
) where
    F: RichField + Extendable<D>,
    FE: FieldExtension<D2, BaseField = F>,
    P: PackedField<Scalar = FE>,
    C: GenericConfig<D, F = F>,
    S: Stark<F, D>,
{
    let degree = stark.constraint_degree();
    let challenge = P::from(challenge);
    for lookup in stark.lookups() {
        let num_helper_columns = lookup_vars.local_values.len();
        for j in 0..num_helper_columns - 2 {
            let mut x = lookup_vars.local_values[j];
            let mut y = P::ZEROS;
            let fs = ((degree - 1) * j..(degree - 1) * (j + 1))
                .map(|k| vars.local_values[lookup.columns[k]]);
            for f in fs {
                x *= challenge + f;
                y += challenge + f;
            }
            yield_constr.constraint(x - y);
        }
        let x = lookup_vars.local_values[num_helper_columns - 2];
        let x = x * (challenge + vars.local_values[lookup.table_column]);
        yield_constr.constraint(x - P::ONES);

        let z = lookup_vars.local_values[num_helper_columns - 1];
        let next_z = lookup_vars.next_values[num_helper_columns - 1];
        let y = lookup_vars.local_values[..num_helper_columns - 2]
            .iter()
            .fold(P::ZEROS, |acc, x| acc + *x);
        -vars.local_values[lookup.table_column] * lookup_vars.local_values[num_helper_columns - 2];
        yield_constr.constraint(next_z - z - y);
    }
}

pub(crate) fn eval_lookups_circuit<
    F: RichField + Extendable<D>,
    const D: usize,
    const COLS: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    vars: StarkEvaluationTargets<D, COLS>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    col_permuted_input: usize,
    col_permuted_table: usize,
) {
    // let local_perm_input = vars.local_values[col_permuted_input];
    // let next_perm_table = vars.next_values[col_permuted_table];
    // let next_perm_input = vars.next_values[col_permuted_input];
    //
    // // A "vertical" diff between the local and next permuted inputs.
    // let diff_input_prev = builder.sub_extension(next_perm_input, local_perm_input);
    // // A "horizontal" diff between the next permuted input and permuted table value.
    // let diff_input_table = builder.sub_extension(next_perm_input, next_perm_table);
    //
    // let diff_product = builder.mul_extension(diff_input_prev, diff_input_table);
    // yield_constr.constraint(builder, diff_product);
    //
    // // This is actually constraining the first row, as per the spec, since `diff_input_table`
    // // is a diff of the next row's values. In the context of `constraint_last_row`, the next
    // // row is the first row.
    // yield_constr.constraint_last_row(builder, diff_input_table);
}
//
// /// Given an input column and a table column, generate the permuted input and permuted table columns
// /// used in the Halo2 permutation argument.
// pub fn permuted_cols<F: PrimeField64>(inputs: &[F], table: &[F]) -> (Vec<F>, Vec<F>) {
//     let n = inputs.len();
//
//     // The permuted inputs do not have to be ordered, but we found that sorting was faster than
//     // hash-based grouping. We also sort the table, as this helps us identify "unused" table
//     // elements efficiently.
//
//     // To compare elements, e.g. for sorting, we first need them in canonical form. It would be
//     // wasteful to canonicalize in each comparison, as a single element may be involved in many
//     // comparisons. So we will canonicalize once upfront, then use `to_noncanonical_u64` when
//     // comparing elements.
//
//     let sorted_inputs = inputs
//         .iter()
//         .map(|x| x.to_canonical())
//         .sorted_unstable_by_key(|x| x.to_noncanonical_u64())
//         .collect_vec();
//     let sorted_table = table
//         .iter()
//         .map(|x| x.to_canonical())
//         .sorted_unstable_by_key(|x| x.to_noncanonical_u64())
//         .collect_vec();
//
//     let mut unused_table_inds = Vec::with_capacity(n);
//     let mut unused_table_vals = Vec::with_capacity(n);
//     let mut permuted_table = vec![F::ZERO; n];
//     let mut i = 0;
//     let mut j = 0;
//     while (j < n) && (i < n) {
//         let input_val = sorted_inputs[i].to_noncanonical_u64();
//         let table_val = sorted_table[j].to_noncanonical_u64();
//         match input_val.cmp(&table_val) {
//             Ordering::Greater => {
//                 unused_table_vals.push(sorted_table[j]);
//                 j += 1;
//             }
//             Ordering::Less => {
//                 if let Some(x) = unused_table_vals.pop() {
//                     permuted_table[i] = x;
//                 } else {
//                     unused_table_inds.push(i);
//                 }
//                 i += 1;
//             }
//             Ordering::Equal => {
//                 permuted_table[i] = sorted_table[j];
//                 i += 1;
//                 j += 1;
//             }
//         }
//     }
//
//     unused_table_vals.extend_from_slice(&sorted_table[j..n]);
//     unused_table_inds.extend(i..n);
//
//     for (ind, val) in unused_table_inds.into_iter().zip_eq(unused_table_vals) {
//         permuted_table[ind] = val;
//     }
//
//     (sorted_inputs, permuted_table)
// }
