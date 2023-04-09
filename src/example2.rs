#![allow(clippy::type_complexity)]

use halo2_proofs::{
    arithmetic::FieldExt, circuit::*, dev::MockProver, pasta::Fp, plonk::*, poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Debug, Clone)]
struct FiboConfig {
    advice: Column<Advice>,
    selector: Selector,
    instance: Column<Instance>,
}

struct FiboChip<F: FieldExt> {
    config: FiboConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FiboChip<F> {
    fn construct(config: FiboConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>, instance: Column<Instance>) -> FiboConfig {
        let advice = meta.advice_column();
        let selector = meta.selector();

        meta.enable_equality(advice);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // advice | selector
            //   a    |    s
            //   b    |
            //   c    |
            //
            let a = meta.query_advice(advice, Rotation::cur());
            let b = meta.query_advice(advice, Rotation::next());
            let c = meta.query_advice(advice, Rotation(2));

            let s = meta.query_selector(selector);

            vec![s * (a + b - c)]
        });

        FiboConfig {
            advice,
            selector,
            instance,
        }
    }

    fn assign_column(
        &self,
        mut layouter: impl Layouter<F>,
        a: Option<F>,
        b: Option<F>,
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        let out = layouter.assign_region(
            || "whole column",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                self.config.selector.enable(&mut region, 1)?;

                let mut a_cell = region.assign_advice(
                    || "a",
                    self.config.advice,
                    0,
                    || a.ok_or(Error::Synthesis),
                )?;

                let mut b_cell = region.assign_advice(
                    || "b",
                    self.config.advice,
                    1,
                    || b.ok_or(Error::Synthesis),
                )?;

                for row in 2..nrows {
                    if row < nrows - 2 {
                        self.config.selector.enable(&mut region, row)?;
                    }
                    let c_val = a_cell.value().and_then(|a| b_cell.value().map(|b| *a + *b));

                    let c_cell = region.assign_advice(
                        || "c",
                        self.config.advice,
                        row,
                        || c_val.ok_or(Error::Synthesis),
                    )?;

                    a_cell = b_cell;
                    b_cell = c_cell;
                }

                Ok(b_cell)
            },
        )?;

        Ok(out)
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
struct MyCircuit<F: FieldExt> {
    a: Option<F>,
    b: Option<F>,
}

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
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

        let out = chip.assign_column(layouter.namespace(|| "whole column"), self.a, self.b, 10)?;

        chip.expose_public(layouter.namespace(|| "out"), &out, 0)?;

        Ok(())
    }
}

fn main() {
    let k = 5;

    let a = Fp::from(1);
    let b = Fp::from(1);

    let circuit = MyCircuit {
        a: Some(a),
        b: Some(b),
    };

    let pub_input = vec![Fp::from(55)];

    let prover = MockProver::run(k, &circuit, vec![pub_input]).unwrap();
    prover.assert_satisfied();
}
