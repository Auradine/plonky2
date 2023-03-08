#![allow(clippy::many_single_char_names)]

use core::convert::TryInto;
use std::fmt::Write;
use std::num::ParseIntError;

use arrayref::{array_mut_ref, array_ref};
use plonky2_field::polynomial::PolynomialValues;
use plonky2_field::types::Field;

use super::constants::{HASH_IV, ROUND_CONSTANTS};
use crate::sha256_stark::layout::*;
use crate::util::trace_rows_to_poly_values;

pub fn decode_hex(s: &str) -> Result<Vec<u8>, ParseIntError> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16))
        .collect()
}
pub fn encode_hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for &b in bytes {
        write!(&mut s, "{:02x}", b).unwrap();
    }
    s
}

fn is_power_of_two(n: u64) -> bool {
    n & (n - 1) == 0
}

#[repr(transparent)]
pub struct Sha2Trace<F: Field>(Vec<[F; NUM_COLS]>);

impl<F: Field> Sha2Trace<F> {
    pub fn new(max_rows: usize) -> Sha2Trace<F> {
        assert!(
            is_power_of_two(max_rows as u64),
            "max_rows must be a power of two"
        );
        Sha2Trace(vec![[F::ZERO; NUM_COLS]; max_rows])
    }
}

pub struct Sha2TraceGenerator<F: Field> {
    trace: Sha2Trace<F>,
    hash_idx: usize,
    step: usize,
}

impl<F: Field> Sha2TraceGenerator<F> {
    pub fn new(max_rows: usize) -> Sha2TraceGenerator<F> {
        Sha2TraceGenerator {
            trace: Sha2Trace::new(max_rows),
            hash_idx: 1, // hash_idx is 1-indexed
            step: 0,
        }
    }

    fn max_rows(&self) -> usize {
        self.trace.0.len()
    }

    fn curr_row_idx(&self) -> usize {
        (self.hash_idx - 1) * NUM_STEPS_PER_HASH + self.step
    }

    fn get_next_window(&mut self) -> (&mut [[F; NUM_COLS]; 2], usize, usize) {
        let idx = self.curr_row_idx();
        assert!(idx < self.max_rows(), "get_next_window exceeded MAX_ROWS");

        let hash_idx = self.hash_idx;
        let step = self.step;
        self.step += 1;

        (array_mut_ref![self.trace.0, idx, 2], hash_idx, step)
    }

    fn get_next_row(&mut self) -> (&mut [F; NUM_COLS], usize, usize) {
        let idx = self.curr_row_idx();
        assert!(idx < self.max_rows(), "get_next_window exceeded MAX_ROWS");

        let hash_idx = self.hash_idx;
        let step = self.step;
        self.step += 1;

        (&mut self.trace.0[idx], hash_idx, step)
    }

    // returns wi
    fn gen_msg_schedule(next_row: &mut [F; NUM_COLS], w15: u32, w2: u32, w16: u32, w7: u32) -> u32 {
        let mut xor_tmp_0 = rotr(w15, 7) ^ rotr(w15, 18);
        let mut s0 = xor_tmp_0 ^ (w15 >> 3);

        let mut xor_tmp_1 = rotr(w2, 17) ^ rotr(w2, 19);
        let mut s1 = xor_tmp_1 ^ (w2 >> 10);

        let mut wi = w16.wrapping_add(s0).wrapping_add(w7).wrapping_add(s1);
        let res = wi;
        let wi_u64 = w16 as u64 + s0 as u64 + w7 as u64 + s1 as u64;
        let quotient = wi_u64 / (1 << 32);
        for bit in 0..32 {
            next_row[xor_tmp_i_bit(0, bit)] = F::from_canonical_u32(xor_tmp_0 & 1);
            next_row[xor_tmp_i_bit(1, bit)] = F::from_canonical_u32(xor_tmp_1 & 1);

            next_row[little_s0_bit(bit)] = F::from_canonical_u32(s0 & 1);
            next_row[little_s1_bit(bit)] = F::from_canonical_u32(s1 & 1);

            next_row[wi_bit(15, bit)] = F::from_canonical_u32(wi & 1);

            xor_tmp_0 >>= 1;
            xor_tmp_1 >>= 1;
            s0 >>= 1;
            s1 >>= 1;
            wi >>= 1;
        }

        next_row[WI_FIELD] = F::from_canonical_u64(wi_u64);
        next_row[WI_QUOTIENT] = F::from_canonical_u64(quotient);

        res
    }

    // returns new (abcd, efgh)
    fn gen_round_fn(
        curr_row: &mut [F; NUM_COLS],
        next_row: &mut [F; NUM_COLS],
        wi: u32,
        ki: u32,
        abcd: [u32; 4],
        efgh: [u32; 4],
    ) -> ([u32; 4], [u32; 4]) {
        let mut xor_tmp_2 = rotr(efgh[0], 6) ^ rotr(efgh[0], 11);
        let mut s1 = xor_tmp_2 ^ rotr(efgh[0], 25);
        let mut ch = (efgh[0] & efgh[1]) ^ ((!efgh[0]) & efgh[2]);
        let mut e_and_f = efgh[0] & efgh[1];
        let mut not_e_and_g = (!efgh[0]) & efgh[2];
        let mut xor_tmp_3 = rotr(abcd[0], 2) ^ rotr(abcd[0], 13);
        let mut s0 = xor_tmp_3 ^ rotr(abcd[0], 22);
        let mut xor_tmp_4 = (abcd[0] & abcd[1]) ^ (abcd[0] & abcd[2]);
        let mut maj = xor_tmp_4 ^ (abcd[1] & abcd[2]);
        let mut a_and_b = abcd[0] & abcd[1];
        let mut a_and_c = abcd[0] & abcd[2];
        let mut b_and_c = abcd[1] & abcd[2];

        let temp1_u32 = efgh[3]
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add(ki)
            .wrapping_add(wi);
        let temp2_u32 = s0.wrapping_add(maj);
        let temp1_u64 = efgh[3] as u64 + s1 as u64 + ch as u64 + ki as u64 + wi as u64;
        let temp2_u64 = s0 as u64 + maj as u64;

        for bit in 0..32 {
            curr_row[xor_tmp_i_bit(2, bit)] = F::from_canonical_u32(xor_tmp_2 & 1);
            curr_row[xor_tmp_i_bit(3, bit)] = F::from_canonical_u32(xor_tmp_3 & 1);
            curr_row[xor_tmp_i_bit(4, bit)] = F::from_canonical_u32(xor_tmp_4 & 1);

            curr_row[big_s1_bit(bit)] = F::from_canonical_u32(s1 & 1);
            curr_row[big_s0_bit(bit)] = F::from_canonical_u32(s0 & 1);
            curr_row[ch_bit(bit)] = F::from_canonical_u32(ch & 1);
            curr_row[maj_bit(bit)] = F::from_canonical_u32(maj & 1);

            curr_row[e_and_f_bit(bit)] = F::from_canonical_u32(e_and_f & 1);
            curr_row[not_e_and_g_bit(bit)] = F::from_canonical_u32(not_e_and_g & 1);
            curr_row[a_and_b_bit(bit)] = F::from_canonical_u32(a_and_b & 1);
            curr_row[a_and_c_bit(bit)] = F::from_canonical_u32(a_and_c & 1);
            curr_row[b_and_c_bit(bit)] = F::from_canonical_u32(b_and_c & 1);

            xor_tmp_2 >>= 1;
            xor_tmp_3 >>= 1;
            xor_tmp_4 >>= 1;
            s1 >>= 1;
            s0 >>= 1;
            ch >>= 1;
            maj >>= 1;
            e_and_f >>= 1;
            not_e_and_g >>= 1;
            a_and_b >>= 1;
            a_and_c >>= 1;
            b_and_c >>= 1;
        }

        let (mut abcd, mut efgh) = swap(abcd, efgh);

        let a_next_u64 = temp1_u64 + temp2_u64;
        let a_next_quotient = a_next_u64 / (1 << 32);
        let e_next_u64 = efgh[0] as u64 + temp1_u64;
        let e_next_quotient = e_next_u64 / (1 << 32);

        abcd[0] = temp1_u32.wrapping_add(temp2_u32);
        efgh[0] = efgh[0].wrapping_add(temp1_u32);

        let res = (abcd.clone(), efgh.clone());

        curr_row[A_NEXT_FIELD] = F::from_canonical_u64(a_next_u64);
        curr_row[A_NEXT_QUOTIENT] = F::from_canonical_u64(a_next_quotient);
        curr_row[E_NEXT_FIELD] = F::from_canonical_u64(e_next_u64);
        curr_row[E_NEXT_QUOTIENT] = F::from_canonical_u64(e_next_quotient);

        for bit in 0..32 {
            next_row[a_bit(bit)] = F::from_canonical_u32(abcd[0] & 1);
            next_row[b_bit(bit)] = F::from_canonical_u32(abcd[1] & 1);
            next_row[c_bit(bit)] = F::from_canonical_u32(abcd[2] & 1);
            next_row[d_bit(bit)] = F::from_canonical_u32(abcd[3] & 1);
            next_row[e_bit(bit)] = F::from_canonical_u32(efgh[0] & 1);
            next_row[f_bit(bit)] = F::from_canonical_u32(efgh[1] & 1);
            next_row[g_bit(bit)] = F::from_canonical_u32(efgh[2] & 1);
            next_row[h_bit(bit)] = F::from_canonical_u32(efgh[3] & 1);

            abcd[0] >>= 1;
            abcd[1] >>= 1;
            abcd[2] >>= 1;
            abcd[3] >>= 1;
            efgh[0] >>= 1;
            efgh[1] >>= 1;
            efgh[2] >>= 1;
            efgh[3] >>= 1;
        }

        res
    }

    // fills in stuff the other fns don't at each row
    fn gen_misc(curr_row: &mut [F; NUM_COLS], step: usize, hash_idx: usize) {
        curr_row[HASH_IDX] = F::from_canonical_u64(hash_idx as u64);

        for i in 0..NUM_STEPS_PER_HASH {
            curr_row[step_bit(i)] = F::ZERO;
        }

        curr_row[step_bit(step)] = F::ONE;
    }

    fn gen_keep_his_same(curr_row: &mut [F; NUM_COLS], next_row: &mut [F; NUM_COLS]) {
        for i in 0..8 {
            next_row[h_i(i)] = curr_row[h_i(i)]
        }
    }
    // returns wis, abcd, efgh
    fn gen_phase_0(
        &mut self,
        his: [u32; 8],
        left_input: [u32; 16],
    ) -> ([u32; 16], [u32; 4], [u32; 4]) {
        let mut abcd = *array_ref![his, 0, 4];
        let mut efgh = *array_ref![his, 4, 4];

        let mut wis = [0; 16];
        for i in 0..16 {
            wis[i] = left_input[i];
        }
        wis = rotl_wis(wis);

        // left inputs
        for i in 0..16 {
            let ([curr_row, next_row], hash_idx, step) = self.get_next_window();

            if i == 0 {
                let mut abcd = abcd;
                let mut efgh = efgh;
                for bit in 0..32 {
                    curr_row[a_bit(bit)] = F::from_canonical_u32(abcd[0] & 1);
                    curr_row[b_bit(bit)] = F::from_canonical_u32(abcd[1] & 1);
                    curr_row[c_bit(bit)] = F::from_canonical_u32(abcd[2] & 1);
                    curr_row[d_bit(bit)] = F::from_canonical_u32(abcd[3] & 1);
                    curr_row[e_bit(bit)] = F::from_canonical_u32(efgh[0] & 1);
                    curr_row[f_bit(bit)] = F::from_canonical_u32(efgh[1] & 1);
                    curr_row[g_bit(bit)] = F::from_canonical_u32(efgh[2] & 1);
                    curr_row[h_bit(bit)] = F::from_canonical_u32(efgh[3] & 1);

                    abcd[0] >>= 1;
                    abcd[1] >>= 1;
                    abcd[2] >>= 1;
                    abcd[3] >>= 1;
                    efgh[0] >>= 1;
                    efgh[1] >>= 1;
                    efgh[2] >>= 1;
                    efgh[3] >>= 1;
                }

                // set his to IV
                for j in 0..8 {
                    curr_row[h_i(j)] = F::from_canonical_u32(HASH_IV[j]);
                }

                // load inputs
                for j in 0..16 {
                    curr_row[input_i(j)] = F::from_canonical_u32(left_input[j])
                        + F::from_canonical_u64(hash_idx as u64) * F::from_canonical_u64(1 << 32);
                }

                // load rotated wis
                let mut wis = wis;
                for j in 0..16 {
                    for bit in 0..32 {
                        curr_row[wi_bit(j, bit)] = F::from_canonical_u32(wis[j] & 1);
                        wis[j] >>= 1;
                    }
                }
            }

            Self::gen_misc(curr_row, step, hash_idx);
            Self::gen_keep_his_same(curr_row, next_row);

            let ki = ROUND_CONSTANTS[i];
            curr_row[KI] = F::from_canonical_u32(ki);
            (abcd, efgh) = Self::gen_round_fn(curr_row, next_row, wis[15], ki, abcd, efgh);

            if i == 15 {
                let w16 = wis[0];
                wis = shift_wis(wis);
                let wi = Self::gen_msg_schedule(next_row, wis[0], wis[13], w16, wis[8]);
                wis[15] = wi;

                // shift wis left
                for i in 0..15 {
                    for bit in 0..32 {
                        next_row[wi_bit(i, bit)] = curr_row[wi_bit(i + 1, bit)];
                    }
                }
            } else {
                wis = rotl_wis(wis);

                // rotate wis left
                for i in 0..16 {
                    for bit in 0..32 {
                        next_row[wi_bit(i, bit)] = curr_row[wi_bit((i + 1) % 16, bit)];
                    }
                }
            }
        }

        (wis, abcd, efgh)
    }

    // returns wis, abcd, efgh, his
    fn gen_phase_1(
        &mut self,
        mut wis: [u32; 16],
        mut abcd: [u32; 4],
        mut efgh: [u32; 4],
        mut his: [u32; 8],
    ) -> ([u32; 16], [u32; 4], [u32; 4], [u32; 8]) {
        for i in 0..48 {
            let ([curr_row, next_row], hash_idx, step) = self.get_next_window();
            Self::gen_misc(curr_row, step, hash_idx);

            let ki = ROUND_CONSTANTS[i + 16];
            curr_row[KI] = F::from_canonical_u32(ki);
            (abcd, efgh) = Self::gen_round_fn(curr_row, next_row, wis[15], ki, abcd, efgh);

            let w16 = wis[0];
            wis = shift_wis(wis);

            if i != 47 {
                Self::gen_keep_his_same(curr_row, next_row);
                let wi = Self::gen_msg_schedule(next_row, wis[0], wis[13], w16, wis[8]);
                wis[15] = wi;
            }

            // update his during last row
            if i == 47 {
                for j in 0..4 {
                    let hj_next_u64 = his[j] as u64 + abcd[j] as u64;
                    let hj_next_quotient = hj_next_u64 / (1 << 32);

                    his[j] = his[j].wrapping_add(abcd[j]);
                    curr_row[h_i_next_field(j)] = F::from_canonical_u64(hj_next_u64);
                    curr_row[h_i_next_quotient(j)] = F::from_canonical_u64(hj_next_quotient);
                    next_row[h_i(j)] = F::from_canonical_u32(his[j]);
                }

                for j in 0..4 {
                    let hj_next_u64 = his[j + 4] as u64 + efgh[j] as u64;
                    let hj_next_quotient = hj_next_u64 / (1 << 32);

                    his[j + 4] = his[j + 4].wrapping_add(efgh[j]);
                    curr_row[h_i_next_field(j + 4)] = F::from_canonical_u64(hj_next_u64);
                    curr_row[h_i_next_quotient(j + 4)] = F::from_canonical_u64(hj_next_quotient);
                    next_row[h_i(j + 4)] = F::from_canonical_u32(his[j + 4]);
                }
            }

            // shift wis left by one
            for i in 0..15 {
                for bit in 0..32 {
                    next_row[wi_bit(i, bit)] = curr_row[wi_bit(i + 1, bit)];
                }
            }
        }

        (wis, abcd, efgh, his)
    }

    fn gen_last_step(&mut self, his: [u32; 8]) {
        let (curr_row, hash_idx, step) = self.get_next_row();
        Self::gen_misc(curr_row, step, hash_idx);
        for i in 0..8 {
            curr_row[output_i(i)] = F::from_canonical_u32(his[i])
                + F::from_canonical_u64(hash_idx as u64) * F::from_canonical_u64(1 << 32);
        }

        // debug code
        // let mut hex_str: String = "".to_owned();
        // for i in 0..8 {
        //     let my_str = format!("{:?}", curr_row[output_i(i)]);
        //     let my_res = my_str.parse::<i64>();
        //     let my_int = my_res.unwrap();
        //     let hex_str0 = format!("{:x}", my_int & 0xffffffff);
        //     hex_str = format!("{}{}", hex_str, hex_str0);
        //     // println!("hex_str0 = {}", hex_str0);
        // }
        // println!("hex_str = {}", hex_str);
    }

    pub fn gen_hash<const N: usize>(&mut self, left_input: [u32; 16 * N]) -> [u32; 8] {
        let mut his = HASH_IV;

        for i in 0..N {
            let mut left_input0: [u32; 16] = [0 as u32; 16];
            for j in 0..16 {
                left_input0[j] = left_input[i * 16 + j];
            }
            let (wis, abcd, efgh) = self.gen_phase_0(his, left_input0);
            let (_wis, _abcd, _efgh, _his) = self.gen_phase_1(wis, abcd, efgh, his);
            his = _his;
            self.gen_last_step(his);
            self.hash_idx += 1;
            self.step = 0;
        }
        his
    }

    pub fn into_polynomial_values(self) -> Vec<PolynomialValues<F>> {
        trace_rows_to_poly_values(self.trace.0)
    }
}

pub fn to_u32_array_be<const N: usize>(block: [u8; N * 4]) -> [u32; N] {
    let mut block_u32 = [0; N];
    for (o, chunk) in block_u32.iter_mut().zip(block.chunks_exact(4)) {
        *o = u32::from_be_bytes(chunk.try_into().unwrap());
    }
    block_u32
}

#[inline(always)]
fn shift_wis(mut wis: [u32; 16]) -> [u32; 16] {
    for i in 0..15 {
        wis[i] = wis[i + 1];
    }
    wis[15] = 0;
    wis
}

#[inline(always)]
fn rotl_wis(wis: [u32; 16]) -> [u32; 16] {
    let mut res = wis;
    for i in 0..16 {
        res[i] = wis[(i + 1) % 16];
    }
    res
}

#[inline(always)]
fn swap(abcd: [u32; 4], efgh: [u32; 4]) -> ([u32; 4], [u32; 4]) {
    (
        [0, abcd[0], abcd[1], abcd[2]],
        [abcd[3], efgh[0], efgh[1], efgh[2]],
    )
}

#[inline(always)]
fn rotr(x: u32, n: u32) -> u32 {
    x.rotate_right(n)
}

#[cfg(test)]
mod tests {
    use generic_array::typenum::U64;
    use generic_array::GenericArray;
    use plonky2_field::goldilocks_field::GoldilocksField;
    use sha2::compress256;

    use super::*;

    type F = GoldilocksField;

    #[test]
    fn test_hash_of_zero() {
        let block = [0u8; 64];
        let block_arr = GenericArray::<u8, U64>::from(block);
        let mut state = HASH_IV;
        compress256(&mut state, &[block_arr]);

        let left_input = [0u32; 16];
        let mut generator = Sha2TraceGenerator::<F>::new(128);

        let his = generator.gen_hash::<1>(left_input);

        assert_eq!(his, state);
    }

    #[test]
    fn test_hash_of_something() {
        let mut block = [0u8; 64];
        for i in 0..64 {
            block[i] = i as u8;
        }

        let block_arr = GenericArray::<u8, U64>::from(block);
        let mut state = HASH_IV;
        compress256(&mut state, &[block_arr]);

        let block: [u32; 16] = to_u32_array_be(block);
        let left_input = *array_ref![block, 0, 16];
        let mut generator = Sha2TraceGenerator::<F>::new(128);

        let his = generator.gen_hash::<1>(left_input);
        assert_eq!(his, state);
    }

    #[test]
    fn test_hash_of_abc() {
        let block0 = decode_hex("61626380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018").unwrap();
        let mut block = [0u8; 64];
        for i in 0..64 {
            block[i] = block0[i];
        }
        let block_arr = GenericArray::<u8, U64>::from(block);
        let mut state = HASH_IV;
        compress256(&mut state, &[block_arr]);

        let block: [u32; 16] = to_u32_array_be(block);
        let left_input = *array_ref![block, 0, 16];
        let mut generator = Sha2TraceGenerator::<F>::new(128);

        let his = generator.gen_hash::<1>(left_input);

        // ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
        print!("\nfinal hash : ");
        for i in 0..8 {
            let x = his[i];
            print!("{:x}", x);
        }
        println!("");

        assert_eq!(his, state);
    }

    // padded message =  010001050303af1c7045f3457951a330683e8ed7304504b3de9ab866a3a3b300f9b4d769311e2098a060686c2ba52707ef471dac9178891cb0c288698ead6984051050c2e34391000c00ff1301c02bc02f009e009c010000b00016000000170000000d00220020060305030403030302030806080b0805080a0804080906010501040103010201002b000302030400330047004500170041045f413967369ad03b0003fca54f79c018e6a726ad459c34aa5ef9e4061a09b4a0ce212c30bf14ad0f2b9f6a4837bf9308c9c042c43e3740bfb0285f0aaa285a11002d0003020100000b00020100000a000e000c001701000101010201030104000f000101001c00024001000900020100020000970303e618a9dfeb826fdd66757813149920579ca3b0cd566fd60ac4668268827f6c622098a060686c2ba52707ef471dac9178891cb0c288698ead6984051050c2e34391130100004f003300450017004104ecfe6e4489100f404beb822b6d065de083b0bf9474c4dcf4541b52da11685c1d98afca65695e94a06376f29daceff0e3221debbe0716ec94dbcb45ed51dfaac3002b000203040800000200000b0009df000009db00058a308205863082050da003020102021005076f66d11b692256ccacd546ffec53300a06082a8648ce3d0403033056310b300906035504061302555331153013060355040a130c446967694365727420496e633130302e06035504031327446967694365727420544c53204879627269642045434320534841333834203230323020434131301e170d3231303131313030303030305a170d3232303131383233353935395a3072310b3009060355040613025553311330110603550408130a43616c69666f726e6961311630140603550407130d53616e204672616e636973636f31193017060355040a1310436c6f7564666c6172652c20496e632e311b301906035504031312636c6f7564666c6172652d646e732e636f6d3059301306072a8648ce3d020106082a8648ce3d0301070342000417ad1fe835af70d38d9c9e64fd471e5b970c0ad110a826321136664d1299c3e131bbf5216373dda5c1c1a0f06da4c45ee1c2dbdaf90d34801af7b9e03af2d574a382039f3082039b301f0603551d230418301680140abc0829178ca5396d7a0ece33c72eb3edfbc37a301d0603551d0e04160414e1b6fc06f9b98b05f4c1e2489b02b90bc1b53d793081a60603551d1104819e30819b8212636c6f7564666c6172652d646e732e636f6d82142a2e636c6f7564666c6172652d646e732e636f6d820f6f6e652e6f6e652e6f6e652e6f6e658704010101018704010000018704a29f24018704a29f2e01871026064700470000000000000000001111871026064700470000000000000000001001871026064700470000000000000000000064871026064700470000000000000000006400300e0603551d0f0101ff040403020780301d0603551d250416301406082b0601050507030106082b060105050703023081970603551d1f04818f30818c3044a042a040863e687474703a2f2f63726c332e64696769636572742e636f6d2f4469676943657274544c53487962726964454343534841333834323032304341312e63726c3044a042a040863e687474703a2f2f63726c342e64696769636572742e636f6d2f4469676943657274544c53487962726964454343534841333834323032304341312e63726c304b0603551d2004443042303606096086480186fd6c01013029302706082b06010505070201161b687474703a2f2f7777772e64696769636572742e636f6d2f4350533008060667810c01020230818306082b0601050507010104773075302406082b060105050730018618687474703a2f2f6f6373702e64696769636572742e636f6d304d06082b060105050730028641687474703a2f2f636163657274732e64696769636572742e636f6d2f4469676943657274544c53487962726964454343534841333834323032304341312e637274300c0603551d130101ff0402300030820104060a2b06010401d6790204020481f50481f200f00076002979bef09e393921f056739f63a577e5be577d9c600af8f94d5d265c255dc78400000176f2e812a80000040300473045022100d1b2f68cf853959de4d453063482028a0aea8aa7bc271efb561ed114641fae67022025b186dd1b2ae78f01c440f6c31678ab61bff63a34fc4788130765f460bb34420076002245450759552456963fa12ff1f76d86e0232663adc04b7f5dc6835c6ee20f0200000176f2e8130f000004030047304502210095dd1a674a2cecac9d6f8bfe3cfea4f53e8725658237379d66bde45d0f68245902207565fe30bb806bcce2b8a18896a8e802268ebecff821faad85a00d87a1d6f134300a06082a8648ce3d0403030367003064023024c2cf6cbdf6aed1c9d51f4a742e3c3dd1c03edcd71bd394715bfea5861626820122d30a6efc98b5d2e2b9e5076977960230457b6f82a67db662c33185d5b5355d4f4c8488ac1a003d0c8440dcb0a7ca1c1327151e37f946c3aed9fdf9b9238b7f2a0000000447308204433082032ba00302010202100a275fe704d6eecb23d5cd5b4b1a4e04300d06092a864886f70d01010c05003061310b300906035504061302555331153013060355040a130c446967694365727420496e6331193017060355040b13107777772e64696769636572742e636f6d3120301e06035504031317446967694365727420476c6f62616c20526f6f74204341301e170d3230303932333030303030305a170d3330303932323233353935395a3056310b300906035504061302555331153013060355040a130c446967694365727420496e633130302e06035504031327446967694365727420544c532048796272696420454343205348413338342032303230204341313076301006072a8648ce3d020106052b8104002203620004c11bc69a5b98d9a429a0e9d404b5dbeba6b26c55c0ffed98c6492f062751cbbf70c1057ac3b19d8789baadb41317c9a8b483c8b890d1cc7435363c8372b0b5d0f72269c8f180c47b408fcf6887265c3989f14d914dda898be403c343e5bf2f73a38201ae308201aa301d0603551d0e041604140abc0829178ca5396d7a0ece33c72eb3edfbc37a301f0603551d2304183016801403de503556d14cbb66f0a3e21b1bc397b23dd155300e0603551d0f0101ff040403020186301d0603551d250416301406082b0601050507030106082b0601050507030230120603551d130101ff040830060101ff020100307606082b06010505070101046a3068302406082b060105050730018618687474703a2f2f6f6373702e64696769636572742e636f6d304006082b060105050730028634687474703a2f2f636163657274732e64696769636572742e636f6d2f4469676943657274476c6f62616c526f6f7443412e637274307b0603551d1f047430723037a035a0338631687474703a2f2f63726c332e64696769636572742e636f6d2f4469676943657274476c6f62616c526f6f7443412e63726c3037a035a0338631687474703a2f2f63726c342e64696769636572742e636f6d2f4469676943657274476c6f62616c526f6f7443412e63726c30300603551d20042930273007060567810c01013008060667810c0102013008060667810c0102023008060667810c010203300d06092a864886f70d01010c05000382010100de3a971b85bd7b8c0a58e3e3f00b06007aaf44632a7fdd816d1118a6faf73860b1b03962bdb87b2ef008c9925b73df6590b7deb457acc02f1c99674d8b5ef201a1adf79653cdd5df5127370646f26f3c31892c4a16291182e7edb7421493e0d960fa3f1c64cb32c3311724d9af3e556fff0f806f1b0108caa40463c8da534cf21926c4f69ddf5cfa9f9f125ea25d1ff6d8178eb662f81d81b60a3b2b686cf0324e0af7998239b148de0b3a89c75f8d2f273c9c02bc21bd87c670be22bad6cdf44bbd536f7bc29a37d12d047ed3b8cc0d5b84a90c2986afa7d8d61ded0e31e19136fd3c0dface8689ceed1c230dbae6f66dea10a6616242fbf8fe7e067070fc0b00000f00004a04030046304402201ad109b284084dbd51699f4a965b3969ec7a972e14b1e5e79f9dc7a9ff876976022000ea18516c04962f72138d2c1babd86c58f508021e0b3bcd1ff869f7b45bec481400002088c84bf0dcc10547d0b4368d100c1b3e3383eeb5f16a7e91bda186179bbeda758000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005ff8
    // N =  49
    // H3: fb12b7580580d48ad0de4a06cd1b9ff9d40d4ff668cc38812487d01e447bd696
    // sha_256_hash: fb12b7580580d48ad0de4a06cd1b9ff9d40d4ff668cc38812487d01e447bd696

    #[test]
    fn test_hash_of_h3() {
        let block0 = decode_hex("010001050303af1c7045f3457951a330683e8ed7304504b3de9ab866a3a3b300f9b4d769311e2098a060686c2ba52707ef471dac9178891cb0c288698ead6984051050c2e34391000c00ff1301c02bc02f009e009c010000b00016000000170000000d00220020060305030403030302030806080b0805080a0804080906010501040103010201002b000302030400330047004500170041045f413967369ad03b0003fca54f79c018e6a726ad459c34aa5ef9e4061a09b4a0ce212c30bf14ad0f2b9f6a4837bf9308c9c042c43e3740bfb0285f0aaa285a11002d0003020100000b00020100000a000e000c001701000101010201030104000f000101001c00024001000900020100020000970303e618a9dfeb826fdd66757813149920579ca3b0cd566fd60ac4668268827f6c622098a060686c2ba52707ef471dac9178891cb0c288698ead6984051050c2e34391130100004f003300450017004104ecfe6e4489100f404beb822b6d065de083b0bf9474c4dcf4541b52da11685c1d98afca65695e94a06376f29daceff0e3221debbe0716ec94dbcb45ed51dfaac3002b000203040800000200000b0009df000009db00058a308205863082050da003020102021005076f66d11b692256ccacd546ffec53300a06082a8648ce3d0403033056310b300906035504061302555331153013060355040a130c446967694365727420496e633130302e06035504031327446967694365727420544c53204879627269642045434320534841333834203230323020434131301e170d3231303131313030303030305a170d3232303131383233353935395a3072310b3009060355040613025553311330110603550408130a43616c69666f726e6961311630140603550407130d53616e204672616e636973636f31193017060355040a1310436c6f7564666c6172652c20496e632e311b301906035504031312636c6f7564666c6172652d646e732e636f6d3059301306072a8648ce3d020106082a8648ce3d0301070342000417ad1fe835af70d38d9c9e64fd471e5b970c0ad110a826321136664d1299c3e131bbf5216373dda5c1c1a0f06da4c45ee1c2dbdaf90d34801af7b9e03af2d574a382039f3082039b301f0603551d230418301680140abc0829178ca5396d7a0ece33c72eb3edfbc37a301d0603551d0e04160414e1b6fc06f9b98b05f4c1e2489b02b90bc1b53d793081a60603551d1104819e30819b8212636c6f7564666c6172652d646e732e636f6d82142a2e636c6f7564666c6172652d646e732e636f6d820f6f6e652e6f6e652e6f6e652e6f6e658704010101018704010000018704a29f24018704a29f2e01871026064700470000000000000000001111871026064700470000000000000000001001871026064700470000000000000000000064871026064700470000000000000000006400300e0603551d0f0101ff040403020780301d0603551d250416301406082b0601050507030106082b060105050703023081970603551d1f04818f30818c3044a042a040863e687474703a2f2f63726c332e64696769636572742e636f6d2f4469676943657274544c53487962726964454343534841333834323032304341312e63726c3044a042a040863e687474703a2f2f63726c342e64696769636572742e636f6d2f4469676943657274544c53487962726964454343534841333834323032304341312e63726c304b0603551d2004443042303606096086480186fd6c01013029302706082b06010505070201161b687474703a2f2f7777772e64696769636572742e636f6d2f4350533008060667810c01020230818306082b0601050507010104773075302406082b060105050730018618687474703a2f2f6f6373702e64696769636572742e636f6d304d06082b060105050730028641687474703a2f2f636163657274732e64696769636572742e636f6d2f4469676943657274544c53487962726964454343534841333834323032304341312e637274300c0603551d130101ff0402300030820104060a2b06010401d6790204020481f50481f200f00076002979bef09e393921f056739f63a577e5be577d9c600af8f94d5d265c255dc78400000176f2e812a80000040300473045022100d1b2f68cf853959de4d453063482028a0aea8aa7bc271efb561ed114641fae67022025b186dd1b2ae78f01c440f6c31678ab61bff63a34fc4788130765f460bb34420076002245450759552456963fa12ff1f76d86e0232663adc04b7f5dc6835c6ee20f0200000176f2e8130f000004030047304502210095dd1a674a2cecac9d6f8bfe3cfea4f53e8725658237379d66bde45d0f68245902207565fe30bb806bcce2b8a18896a8e802268ebecff821faad85a00d87a1d6f134300a06082a8648ce3d0403030367003064023024c2cf6cbdf6aed1c9d51f4a742e3c3dd1c03edcd71bd394715bfea5861626820122d30a6efc98b5d2e2b9e5076977960230457b6f82a67db662c33185d5b5355d4f4c8488ac1a003d0c8440dcb0a7ca1c1327151e37f946c3aed9fdf9b9238b7f2a0000000447308204433082032ba00302010202100a275fe704d6eecb23d5cd5b4b1a4e04300d06092a864886f70d01010c05003061310b300906035504061302555331153013060355040a130c446967694365727420496e6331193017060355040b13107777772e64696769636572742e636f6d3120301e06035504031317446967694365727420476c6f62616c20526f6f74204341301e170d3230303932333030303030305a170d3330303932323233353935395a3056310b300906035504061302555331153013060355040a130c446967694365727420496e633130302e06035504031327446967694365727420544c532048796272696420454343205348413338342032303230204341313076301006072a8648ce3d020106052b8104002203620004c11bc69a5b98d9a429a0e9d404b5dbeba6b26c55c0ffed98c6492f062751cbbf70c1057ac3b19d8789baadb41317c9a8b483c8b890d1cc7435363c8372b0b5d0f72269c8f180c47b408fcf6887265c3989f14d914dda898be403c343e5bf2f73a38201ae308201aa301d0603551d0e041604140abc0829178ca5396d7a0ece33c72eb3edfbc37a301f0603551d2304183016801403de503556d14cbb66f0a3e21b1bc397b23dd155300e0603551d0f0101ff040403020186301d0603551d250416301406082b0601050507030106082b0601050507030230120603551d130101ff040830060101ff020100307606082b06010505070101046a3068302406082b060105050730018618687474703a2f2f6f6373702e64696769636572742e636f6d304006082b060105050730028634687474703a2f2f636163657274732e64696769636572742e636f6d2f4469676943657274476c6f62616c526f6f7443412e637274307b0603551d1f047430723037a035a0338631687474703a2f2f63726c332e64696769636572742e636f6d2f4469676943657274476c6f62616c526f6f7443412e63726c3037a035a0338631687474703a2f2f63726c342e64696769636572742e636f6d2f4469676943657274476c6f62616c526f6f7443412e63726c30300603551d20042930273007060567810c01013008060667810c0102013008060667810c0102023008060667810c010203300d06092a864886f70d01010c05000382010100de3a971b85bd7b8c0a58e3e3f00b06007aaf44632a7fdd816d1118a6faf73860b1b03962bdb87b2ef008c9925b73df6590b7deb457acc02f1c99674d8b5ef201a1adf79653cdd5df5127370646f26f3c31892c4a16291182e7edb7421493e0d960fa3f1c64cb32c3311724d9af3e556fff0f806f1b0108caa40463c8da534cf21926c4f69ddf5cfa9f9f125ea25d1ff6d8178eb662f81d81b60a3b2b686cf0324e0af7998239b148de0b3a89c75f8d2f273c9c02bc21bd87c670be22bad6cdf44bbd536f7bc29a37d12d047ed3b8cc0d5b84a90c2986afa7d8d61ded0e31e19136fd3c0dface8689ceed1c230dbae6f66dea10a6616242fbf8fe7e067070fc0b00000f00004a04030046304402201ad109b284084dbd51699f4a965b3969ec7a972e14b1e5e79f9dc7a9ff876976022000ea18516c04962f72138d2c1babd86c58f508021e0b3bcd1ff869f7b45bec481400002088c84bf0dcc10547d0b4368d100c1b3e3383eeb5f16a7e91bda186179bbeda758000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005ff8").unwrap();
        assert!(block0.len() % 64 == 0);
        assert!((block0.len() / 64) == 49);
        const N: usize = 49;

        let mut block = [0u8; 64 * N];
        for i in 0..64 * N {
            block[i] = block0[i];
        }

        let block: [u32; 16 * N] = to_u32_array_be(block);
        let left_input = *array_ref![block, 0, 16 * N];
        assert!(8192 > 128 * N);
        let mut generator = Sha2TraceGenerator::<F>::new(8192);

        let his = generator.gen_hash::<N>(left_input);

        // fb12b7580580d48ad0de4a06cd1b9ff9d40d4ff668cc38812487d01e447bd696
        // assert_eq!(his, state);
        print!("\nfinal hash : ");
        for i in 0..8 {
            let x = his[i];
            print!("{:x}", x);
        }
        println!("");
    }
}
