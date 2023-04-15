//! Gadget and chips for the [SHA-256] hash function.
//!
//! [SHA-256]: https://tools.ietf.org/html/rfc6234

use std::convert::TryInto;
use std::ops::Deref;

use crate::{
    AssignedBits, BlockWord, RoundWordDense, State, Table16Chip, Table16Config, BLOCK_SIZE,
    DIGEST_SIZE, STATE,
};
use halo2wrong::{
    halo2::{
        arithmetic::FieldExt,
        circuit::{Chip, Layouter, Value},
        plonk::{ConstraintSystem, Error},
    },
    RegionCtx,
};

/*
/// The output of a SHA-256 circuit invocation.
#[derive(Debug)]
pub struct Sha256Digest<BlockWord>(pub [BlockWord; DIGEST_SIZE]);*/

use maingate::{
    decompose, AssignedValue, MainGate, MainGateConfig, MainGateInstructions, RangeChip,
    RangeConfig, RangeInstructions,
};

#[derive(Debug, Clone)]
pub struct Sha256Config {
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
    table16_config: Table16Config,
    max_byte_size: usize,
    max_round: usize,
}

impl Sha256Config {
    pub fn new(
        main_gate_config: MainGateConfig,
        range_config: RangeConfig,
        table16_config: Table16Config,
        max_byte_size: usize,
    ) -> Self {
        let one_round_size = 4 * BLOCK_SIZE;
        let max_round = if max_byte_size % one_round_size == 0 {
            max_byte_size / one_round_size
        } else {
            max_byte_size / one_round_size + 1
        };

        Self {
            main_gate_config,
            range_config,
            table16_config,
            max_byte_size,
            max_round,
        }
    }
}

pub type AssignedDigest<F> = [AssignedValue<F>; DIGEST_SIZE];

/// A gadget that constrains a SHA-256 invocation. It supports input at a granularity of
/// 32 bits.
#[derive(Debug, Clone)]
pub struct Sha256Chip<F: FieldExt> {
    config: Sha256Config,
    states: Vec<State<F>>,
}

impl<F: FieldExt> Sha256Chip<F> {
    const NUM_LOOKUP_TABLES: usize = 8;
    /// Create a new hasher instance.
    pub fn new(config: Sha256Config) -> Self {
        let states = Vec::new();
        Self { config, states }
    }

    pub fn compute_range_lens() -> (Vec<usize>, Vec<usize>) {
        let composition_bit_lens = vec![
            8 / Self::NUM_LOOKUP_TABLES,
            32 / Self::NUM_LOOKUP_TABLES,
            64 / Self::NUM_LOOKUP_TABLES,
        ];
        (composition_bit_lens, vec![])
    }

    pub fn configure(meta: &mut ConstraintSystem<F>, max_byte_size: usize) -> Sha256Config {
        let main_gate_config = MainGate::configure(meta);

        let (composition_bit_lens, overflow_bit_lens) = Self::compute_range_lens();
        let range_config = RangeChip::configure(
            meta,
            &main_gate_config,
            composition_bit_lens,
            overflow_bit_lens,
        );
        let table16_config = Table16Chip::configure(meta);
        Sha256Config::new(
            main_gate_config,
            range_config,
            table16_config,
            max_byte_size,
        )
    }

    pub fn init(&mut self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        Table16Chip::load(self.config.table16_config.clone(), layouter)?;
        let table16_chip = self.table16_chip();
        let init_state = table16_chip.initialization_vector(layouter)?;
        self.states.push(init_state);
        Ok(())
    }

    pub fn finalize(
        &mut self,
        layouter: &mut impl Layouter<F>,
        inputs: &[u8],
    ) -> Result<(AssignedDigest<F>, Vec<AssignedValue<F>>), Error> {
        let input_byte_size = inputs.len();
        assert!(input_byte_size <= self.config.max_byte_size);
        let input_byte_size_with_9 = input_byte_size + 9;
        let one_round_size = 4 * BLOCK_SIZE;
        let num_round = if input_byte_size_with_9 % one_round_size == 0 {
            input_byte_size_with_9 / one_round_size
        } else {
            input_byte_size_with_9 / one_round_size + 1
        };
        let padded_size = one_round_size * num_round;
        let zero_padding_byte_size = padded_size - input_byte_size - 9;
        let max_byte_size = self.config.max_byte_size;
        let max_round = self.config.max_round;
        let remaining_byte_size = max_byte_size - padded_size;
        assert_eq!(
            remaining_byte_size,
            one_round_size * (max_round - num_round)
        );

        let main_gate = self.main_gate();
        let range_chip = self.range_chip();

        let assigned_num_round = layouter.assign_region(
            || "digest:conbined_inputs",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let assigned_inpu_byte_size = main_gate
                    .assign_value(ctx, Value::known(F::from_u128(input_byte_size as u128)))?;
                /*let assigned_zero_padding_byte_size = main_gate.assign_value(
                    ctx,
                    Value::known(F::from_u128(zero_padding_byte_size as u128)),
                )?;*/

                let assigned_num_round =
                    main_gate.assign_value(ctx, Value::known(F::from_u128(num_round as u128)))?;
                /*let assigned_one_round_size =
                main_gate.assign_constant(ctx, F::from_u128(one_round_size as u128))?;*/
                let assigned_max_round =
                    main_gate.assign_constant(ctx, F::from_u128(max_round as u128))?;

                /*let assigned_padded_size =
                main_gate.mul(ctx, &assigned_one_round_size, &assigned_num_round)?;*/

                // 1. 0<= input_byte_size, num_round < 2^64
                {
                    let range_assigned = range_chip.assign(
                        ctx,
                        assigned_inpu_byte_size.value().map(|v| *v),
                        64 / Self::NUM_LOOKUP_TABLES,
                        64,
                    )?;
                    main_gate.assert_equal(ctx, &assigned_inpu_byte_size, &range_assigned)?;
                }
                {
                    let range_assigned = range_chip.assign(
                        ctx,
                        assigned_num_round.value().map(|v| *v),
                        64 / Self::NUM_LOOKUP_TABLES,
                        64,
                    )?;
                    main_gate.assert_equal(ctx, &assigned_num_round, &range_assigned)?;
                }
                // 2. num_round <= max_round
                {
                    let sub = main_gate.sub(ctx, &assigned_max_round, &assigned_num_round)?;
                    let range_assigned = range_chip.assign(
                        ctx,
                        sub.value().map(|v| *v),
                        64 / Self::NUM_LOOKUP_TABLES,
                        64,
                    )?;
                    main_gate.assert_equal(ctx, &sub, &range_assigned)?;
                }
                // 3. padded_size == inpu_byte_size + zero_padding_byte_size + 9
                /*{
                    let add1 = main_gate.add(
                        ctx,
                        &assigned_inpu_byte_size,
                        &assigned_zero_padding_byte_size,
                    )?;
                    let add2 = main_gate.add_constant(ctx, &add1, F::from_u128(9u128))?;
                    main_gate.assert_equal(ctx, &assigned_padded_size, &add2)?;
                }*/
                Ok(assigned_num_round)
            },
        )?;

        let mut padded_inputs = inputs
            .into_iter()
            .map(|byte| Value::known(*byte))
            .collect::<Vec<Value<u8>>>();
        padded_inputs.push(Value::known(0x80));
        for _ in 0..zero_padding_byte_size {
            padded_inputs.push(Value::known(0));
        }
        let mut input_len_bytes = [0; 8];
        let le_size_bytes = (8 * input_byte_size).to_le_bytes();
        input_len_bytes[0..le_size_bytes.len()].copy_from_slice(&le_size_bytes);
        for byte in input_len_bytes.iter().rev() {
            padded_inputs.push(Value::known(*byte));
        }
        assert_eq!(padded_inputs.len(), num_round * one_round_size);
        for _ in 0..remaining_byte_size {
            padded_inputs.push(Value::known(0));
        }
        assert_eq!(padded_inputs.len(), max_byte_size);

        let assigned_padded_blocks = layouter.assign_region(
            || "digest:assigned_padded_inputs",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                padded_inputs
                    .chunks(4)
                    .map(|vals| {
                        let val_u32: Value<u32> =
                            vals[0].zip(vals[1]).zip(vals[2]).zip(vals[3]).map(
                                |(((v0, v1), v2), v3)| {
                                    (v3 as u32)
                                        + (1u32 << 8) * (v2 as u32)
                                        + (1u32 << 16) * (v1 as u32)
                                        + (1u32 << 24) * (v0 as u32)
                                },
                            );
                        range_chip.assign(
                            ctx,
                            val_u32.map(|v| F::from_u128(v as u128)),
                            32 / Self::NUM_LOOKUP_TABLES,
                            32,
                        )
                    })
                    .collect::<Result<Vec<AssignedValue<F>>, Error>>()
            },
        )?;

        /*let assigned_indexes = layouter.assign_region(
            || "digest:assigned_indexes",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                (0..max_byte_size)
                    .into_iter()
                    .map(|idx| main_gate.assign_constant(ctx, F::from_u128(idx as u128)))
                    .collect::<Result<Vec<AssignedValue<F>>, Error>>()
            },
        )?;
        layouter.assign_region(
            || "digest:assert_padding",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let zero_padding_start =
                    main_gate.add_constant(ctx, &assigned_inpu_byte_size, F::one())?;
                let zero_padding_end =
                    main_gate.add(ctx, &zero_padding_start, &assigned_zero_padding_byte_size)?;
                let len_padding_start = zero_padding_end.clone();
                let len_padding_end =
                    main_gate.add_constant(ctx, &len_padding_start, F::from_u128(8u128))?;
                let one_padding = main_gate.assign_constant(ctx, F::from_u128(0x80u128))?;
                let two_eight = main_gate.assign_constant(ctx, F::from_u128(1u128 << 8))?;
                let two_eight_inv = main_gate.invert_unsafe(ctx, &two_eight)?;
                let mut two_eight_pow =
                    main_gate.assign_constant(ctx, F::from_u128(1u128 << 64))?;
                let mut decomposed_len_acc = main_gate.assign_constant(ctx, F::zero())?;

                for i in 0..max_byte_size {
                    let is_real =
                        self.is_less_than_u64(ctx, &assigned_indexes[i], &assigned_inpu_byte_size)?;
                    let is_padding_one = {
                        let is_valid_len = main_gate.is_equal(
                            ctx,
                            &assigned_indexes[i],
                            &assigned_inpu_byte_size,
                        )?;
                        let is_valid_input =
                            main_gate.is_equal(ctx, &assigned_padded_inputs[i], &one_padding)?;
                        main_gate.and(ctx, &is_valid_len, &is_valid_input)?
                    };
                    let is_zero_padding = {
                        let is_greater_than_or_eq = self.is_greater_than_or_equal_u64(
                            ctx,
                            &assigned_indexes[i],
                            &zero_padding_start,
                        )?;
                        let is_less =
                            self.is_less_than_u64(ctx, &assigned_indexes[i], &zero_padding_end)?;
                        let is_valid_len = main_gate.and(ctx, &is_greater_than_or_eq, &is_less)?;
                        let is_valid_input = main_gate.is_zero(ctx, &assigned_padded_inputs[i])?;
                        main_gate.and(ctx, &is_valid_len, &is_valid_input)?
                    };
                    let is_len_padding = {
                        let is_greater_than_or_eq = self.is_greater_than_or_equal_u64(
                            ctx,
                            &assigned_indexes[i],
                            &len_padding_start,
                        )?;
                        let is_less =
                            self.is_less_than_u64(ctx, &assigned_indexes[i], &len_padding_end)?;
                        let is_valid_len = main_gate.and(ctx, &is_greater_than_or_eq, &is_less)?;
                        is_valid_len
                    };
                    two_eight_pow = {
                        let dived = main_gate.mul(ctx, &two_eight_pow, &two_eight_inv)?;
                        main_gate.select(ctx, &dived, &two_eight_pow, &is_len_padding)?
                    };
                    decomposed_len_acc = {
                        let term =
                            main_gate.mul(ctx, &assigned_padded_inputs[i], &two_eight_pow)?;
                        let added = main_gate.add(ctx, &decomposed_len_acc, &term)?;
                        main_gate.select(ctx, &added, &decomposed_len_acc, &is_len_padding)?
                    };
                    let is_remaining = {
                        let is_valid_len = self.is_greater_than_or_equal_u64(
                            ctx,
                            &assigned_indexes[i],
                            &len_padding_end,
                        )?;
                        let is_valid_input = main_gate.is_zero(ctx, &assigned_padded_inputs[i])?;
                        main_gate.and(ctx, &is_valid_len, &is_valid_input)?
                    };
                    let sel_sum = {
                        let add = main_gate.add(ctx, &is_real, &is_padding_one)?;
                        let add = main_gate.add(ctx, &add, &is_zero_padding)?;
                        let add = main_gate.add(ctx, &add, &is_len_padding)?;
                        let add = main_gate.add(ctx, &add, &is_remaining)?;
                        add
                    };
                    main_gate.assert_one(ctx, &sel_sum)?;
                }

                main_gate.assert_one(ctx, &two_eight_pow)?;
                let eight = main_gate.assign_constant(ctx, F::from_u128(8u128))?;
                let assigned_inpu_bits_size =
                    main_gate.mul(ctx, &assigned_inpu_byte_size, &eight)?;
                main_gate.assert_equal(ctx, &assigned_inpu_bits_size, &decomposed_len_acc)?;

                Ok(())
            },
        )?;*/

        for (i, assigned_blocks) in assigned_padded_blocks.chunks(BLOCK_SIZE).enumerate() {
            let input_blocks = assigned_blocks
                .iter()
                .map(|cell| BlockWord(cell.value().map(|v| v.get_lower_32())))
                .collect::<Vec<BlockWord>>();
            let (new_state, table16_assigned_inputs) =
                self.compute_one_round(layouter, input_blocks.try_into().unwrap())?;
            self.states.push(new_state);

            layouter.assign_region(
                || format!("digest:assigned_u32s:{}", i),
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    for (block1, block2) in assigned_blocks.iter().zip(&table16_assigned_inputs) {
                        ctx.constrain_equal(block1.cell(), block2.cell())?;
                    }
                    Ok(())
                },
            )?;
        }

        let new_digest_values = layouter.assign_region(
            || "digest:new_digest_values",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let assigned_digests = (0..self.config.max_round)
                    .map(|n_round| self.internal_assigned_digest(ctx, n_round + 1))
                    .collect::<Result<Vec<AssignedDigest<F>>, Error>>()?;
                let zero = main_gate.assign_constant(ctx, F::zero())?;
                let mut new_digest_values: [AssignedValue<F>; DIGEST_SIZE] = (0..DIGEST_SIZE)
                    .map(|_| zero.clone())
                    .collect::<Vec<AssignedValue<F>>>()
                    .try_into()
                    .unwrap();
                for n_round in 0..self.config.max_round {
                    let assigned_n_round =
                        main_gate.assign_constant(ctx, F::from_u128(n_round as u128 + 1))?;
                    let is_eq = main_gate.is_equal(ctx, &assigned_n_round, &assigned_num_round)?;
                    for j in 0..DIGEST_SIZE {
                        new_digest_values[j] = main_gate.mul_add(
                            ctx,
                            &is_eq,
                            &assigned_digests[n_round][j],
                            &new_digest_values[j],
                        )?;
                    }
                }
                Ok(new_digest_values)
            },
        )?;

        Ok((new_digest_values, assigned_padded_blocks))
    }

    /// Getter for [`RangeChip`].
    pub fn range_chip(&self) -> RangeChip<F> {
        RangeChip::<F>::new(self.config.range_config.clone())
    }

    /// Getter for [`MainGate`].
    pub fn main_gate(&self) -> MainGate<F> {
        MainGate::<F>::new(self.config.main_gate_config.clone())
    }

    /// Getter for [`Table16Chip`].
    pub fn table16_chip(&self) -> Table16Chip<F> {
        Table16Chip::construct(self.config.table16_config.clone())
    }

    pub fn decompose_digest_to_bytes(
        &self,
        layouter: &mut impl Layouter<F>,
        digest: &[AssignedValue<F>],
    ) -> Result<[AssignedValue<F>; 4 * DIGEST_SIZE], Error> {
        let main_gate = self.main_gate();
        let range_chip = self.range_chip();
        let assigned_bytes = layouter.assign_region(
            || "decompose_digest_to_bytes",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let mut assigned_bytes = Vec::new();
                for word in digest.into_iter() {
                    let mut bytes = range_chip
                        .decompose(ctx, word.value().map(|v| *v), 8, 32)?
                        .1;
                    bytes.reverse();
                    assigned_bytes.append(&mut bytes);
                }

                let u8 = main_gate.assign_constant(ctx, F::from_u128(1u128 << 8))?;
                let u16 = main_gate.assign_constant(ctx, F::from_u128(1u128 << 16))?;
                let u24 = main_gate.assign_constant(ctx, F::from_u128(1u128 << 24))?;
                for (idx, bytes) in assigned_bytes.chunks(32 / 8).enumerate() {
                    let assigned_u32 = main_gate.mul_add(ctx, &u8, &bytes[2], &bytes[3])?;
                    let assigned_u32 = main_gate.mul_add(ctx, &u16, &bytes[1], &assigned_u32)?;
                    let assigned_u32 = main_gate.mul_add(ctx, &u24, &bytes[0], &assigned_u32)?;
                    main_gate.is_equal(ctx, &assigned_u32, &digest[idx])?;
                }
                Ok(assigned_bytes)
            },
        )?;
        Ok(assigned_bytes.try_into().unwrap())
    }

    fn compute_one_round(
        &self,
        layouter: &mut impl Layouter<F>,
        input: [BlockWord; super::BLOCK_SIZE],
    ) -> Result<(State<F>, Vec<AssignedBits<32, F>>), Error> {
        let last_state = self.states.last().unwrap();
        let last_digest = layouter.assign_region(
            || "compute_one_round:last_digest",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                Ok(self.last_assigned_digest(ctx)?)
            },
        )?;
        //let last_digest = self.last_assigned_digest(ctx)?;
        let (compressed_state, assigned_inputs) =
            self.table16_chip().compress(layouter, last_state, input)?;

        let new_state_word_vals = layouter.assign_region(
            || "compute_one_round:new_state_word_vals",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let compressed_state_values =
                    self.state_to_assigned_halves(ctx, &compressed_state)?;
                let main_gate = self.main_gate();
                let range_chip = self.range_chip();

                let word_sums = last_digest
                    .iter()
                    .zip(&compressed_state_values)
                    .map(|(digest_word, comp_word)| main_gate.add(ctx, digest_word, comp_word))
                    .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
                let u32_mod = 1u128 << 32;
                let lo_his = word_sums
                    .iter()
                    .map(|sum| {
                        sum.value()
                            .map(|v| {
                                (
                                    F::from_u128(v.get_lower_128() % u32_mod),
                                    F::from_u128(v.get_lower_128() >> 32),
                                )
                            })
                            .unzip()
                    })
                    .collect::<Vec<(Value<F>, Value<F>)>>();
                let assigned_los = lo_his
                    .iter()
                    .map(|(lo, _)| range_chip.assign(ctx, *lo, 32 / Self::NUM_LOOKUP_TABLES, 32))
                    .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
                let assigned_his = lo_his
                    .iter()
                    .map(|(_, hi)| main_gate.assign_value(ctx, *hi))
                    .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
                let u32 = main_gate.assign_constant(ctx, F::from(1 << 32))?;

                let combines = assigned_los
                    .iter()
                    .zip(&assigned_his)
                    .map(|(lo, hi)| main_gate.mul_add(ctx, hi, &u32, lo))
                    .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
                for (combine, word_sum) in combines.iter().zip(&word_sums) {
                    main_gate.assert_equal(ctx, combine, word_sum)?;
                }

                let mut new_state_word_vals = [Value::unknown(); STATE];
                for i in 0..STATE {
                    new_state_word_vals[i] = assigned_los[i].value().map(|v| v.get_lower_32());
                }
                Ok(new_state_word_vals)
            },
        )?;
        let new_state = self
            .table16_chip()
            .compression_config()
            .initialize_with_iv(layouter, new_state_word_vals)?;

        Ok((new_state, assigned_inputs))
    }

    pub fn last_assigned_digest(&self, ctx: &mut RegionCtx<F>) -> Result<AssignedDigest<F>, Error> {
        self.internal_assigned_digest(ctx, self.states.len() - 1)
    }

    pub fn internal_assigned_digest(
        &self,
        ctx: &mut RegionCtx<F>,
        idx: usize,
    ) -> Result<AssignedDigest<F>, Error> {
        self.state_to_assigned_halves(ctx, &self.states[idx])
    }

    fn state_to_assigned_halves(
        &self,
        ctx: &mut RegionCtx<F>,
        state: &State<F>,
    ) -> Result<[AssignedValue<F>; DIGEST_SIZE], Error> {
        let (a, b, c, d, e, f, g, h) = state.split_state();

        let assigned_cells = [
            self.concat_word_halves(ctx, a.dense_halves())?,
            self.concat_word_halves(ctx, b.dense_halves())?,
            self.concat_word_halves(ctx, c.dense_halves())?,
            self.concat_word_halves(ctx, d)?,
            self.concat_word_halves(ctx, e.dense_halves())?,
            self.concat_word_halves(ctx, f.dense_halves())?,
            self.concat_word_halves(ctx, g.dense_halves())?,
            self.concat_word_halves(ctx, h)?,
        ];
        Ok(assigned_cells)
    }

    fn concat_word_halves(
        &self,
        ctx: &mut RegionCtx<F>,
        word: RoundWordDense<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let (lo, hi) = word.halves();
        let main_gate = self.main_gate();
        let u16 = main_gate.assign_constant(ctx, F::from(1 << 16))?;

        let val_u32 = word.value();
        let val_lo = val_u32.map(|v| F::from_u128((v % (1 << 16)) as u128));
        let val_hi = val_u32.map(|v| F::from_u128((v >> 16) as u128));
        let assigned_lo = main_gate.assign_value(ctx, val_lo)?;
        let assigned_hi = main_gate.assign_value(ctx, val_hi)?;
        ctx.constrain_equal(lo.cell(), assigned_lo.cell())?;
        ctx.constrain_equal(hi.cell(), assigned_hi.cell())?;

        main_gate.mul_add(ctx, &assigned_hi, &u16, &assigned_lo)
    }

    fn is_less_than_u64(
        &self,
        ctx: &mut RegionCtx<F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let main_gate = self.main_gate();
        let inflated_a = main_gate.add_constant(ctx, a, F::from_u128(1 << 64))?;
        let sub = main_gate.sub(ctx, &inflated_a, b)?;
        let sub_bits = main_gate.to_bits(ctx, &sub, 65)?;
        let is_overflow = main_gate.is_zero(ctx, &sub_bits[64])?;
        let is_eq = main_gate.is_equal(ctx, a, b)?;
        let is_not_eq = main_gate.not(ctx, &is_eq)?;
        let is_less = main_gate.and(ctx, &is_overflow, &is_not_eq)?;
        Ok(is_less)
    }

    fn is_greater_than_or_equal_u64(
        &self,
        ctx: &mut RegionCtx<F>,
        a: &AssignedValue<F>,
        b: &AssignedValue<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let is_less = self.is_less_than_u64(ctx, a, b)?;
        self.main_gate().not(ctx, &is_less)
    }
}

#[cfg(test)]
mod test {
    use crate::table16::*;
    use std::marker::PhantomData;

    use super::*;
    use halo2wrong::curves::pasta::pallas;
    use halo2wrong::halo2::plonk::Advice;
    use halo2wrong::halo2::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, Column, ConstraintSystem,
            Error, Instance,
        },
        poly::commitment::Params,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use halo2wrong::utils::fe_to_big;
    use rand::rngs::OsRng;

    struct TestCircuit<F: FieldExt> {
        test_input: Vec<u8>,
        _f: PhantomData<F>,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
        type Config = Sha256Config;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            Sha256Chip::configure(meta, Self::MAX_BYTE_SIZE)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let mut sha256_chip = self.sha256_chip(config.clone());
            sha256_chip.init(&mut layouter)?;
            let range_chip = sha256_chip.range_chip();
            range_chip.load_table(&mut layouter)?;
            let maingate = sha256_chip.main_gate();
            let (digest, assigned_input) = sha256_chip.finalize(&mut layouter, &self.test_input)?;
            let assigned_bytes = sha256_chip.decompose_digest_to_bytes(&mut layouter, &digest)?;
            for (i, cell) in assigned_bytes.iter().enumerate() {
                maingate.expose_public(
                    layouter.namespace(|| format!("region {}", i)),
                    cell.clone(),
                    i,
                )?;
            }

            Ok(())
        }
    }

    impl<F: FieldExt> TestCircuit<F> {
        const MAX_BYTE_SIZE: usize = 128;

        fn sha256_chip(&self, config: Sha256Config) -> Sha256Chip<F> {
            Sha256Chip::new(config)
        }
    }

    use super::super::table16::compression::COMPRESSION_OUTPUT;

    #[test]
    fn test_sha256_correct1() {
        use halo2wrong::curves::pasta::pallas::Base;
        use halo2wrong::halo2::dev::MockProver;

        let k = 17;

        // Test vector: "abc"
        let test_input = vec!['a' as u8, 'b' as u8, 'c' as u8];

        let circuit = TestCircuit::<Base> {
            test_input,
            _f: PhantomData,
        };
        let test_output: [u8; 32] = [
            0b10111010, 0b01111000, 0b00010110, 0b10111111, 0b10001111, 0b00000001, 0b11001111,
            0b11101010, 0b01000001, 0b01000001, 0b01000000, 0b11011110, 0b01011101, 0b10101110,
            0b00100010, 0b00100011, 0b10110000, 0b00000011, 0b01100001, 0b10100011, 0b10010110,
            0b00010111, 0b01111010, 0b10011100, 0b10110100, 0b00010000, 0b11111111, 0b01100001,
            0b11110010, 0b00000000, 0b00010101, 0b10101101,
        ];
        let test_output = test_output.map(|val| Base::from_u128(val as u128));
        let public_inputs = vec![test_output.to_vec()];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_sha256_correct2() {
        use halo2wrong::curves::pasta::pallas::Base;
        use halo2wrong::halo2::dev::MockProver;

        let k = 17;

        // Test vector: "0x0"
        let test_input = vec![0u8];

        let circuit = TestCircuit::<Base> {
            test_input,
            _f: PhantomData,
        };
        let test_output: [u8; 32] = [
            0x6e, 0x34, 0x0b, 0x9c, 0xff, 0xb3, 0x7a, 0x98, 0x9c, 0xa5, 0x44, 0xe6, 0xbb, 0x78,
            0x0a, 0x2c, 0x78, 0x90, 0x1d, 0x3f, 0xb3, 0x37, 0x38, 0x76, 0x85, 0x11, 0xa3, 0x06,
            0x17, 0xaf, 0xa0, 0x1d,
        ];
        let test_output = test_output.map(|val| Base::from_u128(val as u128));
        let public_inputs = vec![test_output.to_vec()];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_sha256_correct3() {
        use halo2wrong::curves::pasta::pallas::Base;
        use halo2wrong::halo2::dev::MockProver;

        let k = 17;

        let test_input = vec![0x1; 60];

        let circuit = TestCircuit::<Base> {
            test_input,
            _f: PhantomData,
        };
        let test_output: [u8; 32] = [
            0x5e, 0x40, 0x84, 0xef, 0xf2, 0xf3, 0x7d, 0x63, 0x7e, 0x65, 0x02, 0xbf, 0x94, 0x72,
            0xb0, 0x02, 0x97, 0x55, 0xbb, 0xd1, 0x30, 0xeb, 0xb5, 0x2c, 0x8c, 0x33, 0xbb, 0x81,
            0x48, 0xc3, 0x1f, 0xd2,
        ];
        let test_output = test_output.map(|val| Base::from_u128(val as u128));
        let public_inputs = vec![test_output.to_vec()];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
