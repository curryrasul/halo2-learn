#![allow(clippy::type_complexity)]

use halo2_proofs::{
    arithmetic::Field, circuit::*, dev::MockProver, halo2curves::bn256::Fr as Fp, plonk::*,
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct FiboConfig {
    col_a: Column<Advice>,
    col_b: Column<Advice>,
    col_c: Column<Advice>,

    selector: Selector,
    instance: Column<Instance>,
}

struct FiboChip<F: Field> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> FiboChip<F> {
    fn construct(config: FiboConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>, instance: Column<Instance>) -> FiboConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();

        let selector = meta.selector();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a       b       c        s
            //
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());

            let s = meta.query_selector(selector);

            vec![s * (a + b - c)]
        });

        FiboConfig {
            col_a,
            col_b,
            col_c,
            selector,
            instance,
        }
    }

    fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
        a: Value<F>,
        b: Value<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        let (a, b, c) = layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let a_cell = region.assign_advice(|| "f(0)", self.config.col_a, 0, || a)?;

                let b_cell = region.assign_advice(|| "f(1)", self.config.col_b, 0, || b)?;

                let c_val = a.and_then(|a| b.map(|b| a + b));

                let c_cell = region.assign_advice(|| "f(2)", self.config.col_c, 0, || c_val)?;

                Ok((a_cell, b_cell, c_cell))
            },
        )?;

        Ok((a, b, c))
    }

    fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        prev_b: &AssignedCell<F, F>,
        prev_c: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let c_cell = layouter.assign_region(
            || format!("{}th row", row),
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                prev_b.copy_advice(|| "a", &mut region, self.config.col_a, 0)?;
                prev_c.copy_advice(|| "b", &mut region, self.config.col_b, 0)?;

                let c_val = prev_b.value().and_then(|b| prev_c.value().map(|c| *b + *c));

                region.assign_advice(|| "c", self.config.col_c, 0, || c_val)
            },
        )?;

        Ok(c_cell)
    }

    fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
struct MyCircuit<F: Field> {
    a: Value<F>,
    b: Value<F>,
}

impl<F: Field> Circuit<F> for MyCircuit<F> {
    type Config = FiboConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let instance = meta.instance_column();
        FiboChip::configure(meta, instance)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FiboChip::construct(config);

        let (_, mut prev_b, mut prev_c) =
            chip.assign_first_row(layouter.namespace(|| "first row"), self.a, self.b)?;

        for i in 3..10 {
            let c_cell = chip.assign_row(
                layouter.namespace(|| format!("{}th row", i)),
                &prev_b,
                &prev_c,
                i,
            )?;

            prev_b = prev_c;
            prev_c = c_cell;
        }

        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 0)?;

        Ok(())
    }
}

fn main() {
    let k = 4;

    let a = Value::known(Fp::from(1));
    let b = Value::known(Fp::from(1));

    let circuit = MyCircuit { a, b };

    let pub_input = vec![Fp::from(55)];

    let prover = MockProver::run(k, &circuit, vec![pub_input]).unwrap();
    prover.assert_satisfied();
}
