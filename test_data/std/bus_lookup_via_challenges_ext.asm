use std::prelude::Query;
use std::convert::fe;
use std::protocols::lookup_via_bus::lookup;
use std::protocols::lookup_via_bus::compute_next_z_send_lookup;
use std::protocols::lookup_via_bus::compute_next_z_receive_lookup;
use std::math::fp2::Fp2;
use std::prover::challenge;

machine Main with degree: 8 {

    let alpha1: expr = challenge(0, 1);
    let alpha2: expr = challenge(0, 2);
    let beta1: expr = challenge(0, 3);
    let beta2: expr = challenge(0, 4);
    let alpha = Fp2::Fp2(alpha1, alpha2);
    let beta = Fp2::Fp2(beta1, beta2);

    col fixed a_sel = [0, 1, 1, 1, 0, 1, 0, 0];
    col fixed b_sel = [1, 1, 0, 1, 1, 1, 1, 0];

    col fixed a1 = [16, 20, 22, 17, 16, 20, 4, 1];
    col fixed a2 = [12, 5, 7, 2, 5, 5, 4, 1];
    col fixed a3 = [20, 36, 38, 33, 36, 36, 4, 3];
    col witness b1, b2, b3;
    query |i| {
        std::prover::provide_value(b1, i, fe(i + 16));
        std::prover::provide_value(b2, i, fe(i + 1));
        std::prover::provide_value(b3, i, fe(i + 32));
    };
    col fixed m = [0, 1, 0, 0, 2, 0, 1, 0];

    let lookup_constraint = a_sel $ [a1, a2, a3] in b_sel $ [b1, b2, b3];

    // TODO: Functions currently cannot add witness columns at later stages,
    // so we have to manually create it here and pass it to lookup(). 
    col witness stage(1) z1;
    col witness stage(1) z2;
    let z = Fp2::Fp2(z1, z2);

    col witness stage(1) u1;
    col witness stage(1) u2;
    let u = Fp2::Fp2(u1, u2);


    lookup(1, [z1,z2], [u1, u2], alpha, beta, lookup_constraint, m);

    let is_first: col = std::well_known::is_first;
    
    col witness stage(1) z1_next;
    col witness stage(1) z2_next;
    query |i| {
        let hint_send = compute_next_z_send_lookup(is_first, 1, z, alpha, beta, lookup_constraint);
        std::prover::provide_value(z1_next, i, hint_send[0]);
        std::prover::provide_value(z2_next, i, hint_send[1]);
    };

    z1' = z1_next;
    z2' = z2_next;

    col witness stage(1) u1_next;
    col witness stage(1) u2_next;
    query |i| {
        let hint_receive = compute_next_z_receive_lookup(is_first, 1, u, alpha, beta, lookup_constraint, m);
        std::prover::provide_value(u1_next, i, hint_receive[0]);
        std::prover::provide_value(u2_next, i, hint_receive[1]);
    };

    u1' = u1_next;
    u2' = u2_next;

    is_first' * (z1 + u1) = 0;
    is_first' * (z2 + u2) = 0;
}
