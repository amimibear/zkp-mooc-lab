pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    assert(b < 254);
    signal input in;
    signal output out;

    // TODO
    signal bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    component ise = IsEqual();
    ise.in[0] <== in;
    ise.in[1] <== sum_of_bits;
    out <== ise.out;
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `b`-bit long `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(b, shift) {
    assert(shift < b);
    signal input x;
    signal output y;

    // TODO
    signal bits[b];
    signal a[shift+1];
    a[0] <== x;
    for (var i = 0; i < b; i++) {
        bits[i] <-- (x >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
        if (i < shift) {
            a[i+1] <-- a[i]\2;
            a[i] === a[i+1]*2 + bits[i];
        }
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === x;
    y <== a[shift];
    
}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    //// Although m_prime is P+1 bits long in no overflow case, it can be P+2 bits long
    //// in the overflow case and the constraints should not fail in either case
    component right_shift = RightShift(P+2, round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift0(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    // TODO
    // component is0 = IsZero();
    // is0.in <== shift;

    // component ls[2];
    // ls[0] = LessThan(13);
    // ls[0].in[0] <== 0;
    // ls[0].in[1] <== shift;

    // (1-ls[0].out) * (1-is0.out) === 0;
    assert(shift < shift_bound || skip_checks);
    assert(shift >= 0 || skip_checks);

    // ls[1] = LessThan(13);
    // ls[1].in[0] <== shift;
    // ls[1].in[1] <== shift_bound;
    // (1-ls[1].out) * (1-skip_checks) === 0;

    signal a[shift_bound+1],o[shift_bound+1];
    component ise[shift_bound+1];
    a[0] <== x;
    o[0] <== 1;
    for (var i = 0; i < shift_bound; i++) {
        ise[i] = IsEqual();
        ise[i].in[0] <== shift;
        ise[i].in[1] <== i;
        o[i+1] <== o[i] * (1-ise[i].out);
        a[i+1] <== a[i] * (1+o[i+1]);
    }
    y <== a[shift_bound];
    // y <-- x << shift;
}

template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    // TODO
    assert(shift < shift_bound || skip_checks);
    assert(shift >= 0 || skip_checks);

    var l = 0;
    while (shift_bound >= (1 << l)) {
        l++;
    }

    component sft = Num2Bits(l);
    sft.in <== shift;
    // log(shift,l,shift_bound);

    signal a[l+1];
    a[0] <== x;
    for (var i = 0; i < l; i++) {
        a[i+1] <== a[i] + (a[i]*(1<<(1<<i)) - a[i]) * sft.bits[i];
    }
    y <== a[l];
}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    // TODO
    assert(in > 0 || skip_checks);
    component ls = LessThan(b);
    ls.in[0] <== 0;
    ls.in[1] <== in;

    (1-ls.out)*(1-skip_checks) === 0;

    component bits = Num2Bits(b);
    bits.in <== in;
    // bits.bits[]
    // component bits[b] = Bit(b);

    component or[b];
    signal a[b+1];
    a[b] <== 0;
    for (var i = b-1; i >= 0; i--) {
        or[i] = OR();
        or[i].a <== bits.bits[i];
        or[i].b <== a[i+1];
        a[i] <== or[i].out;
    }
    for (var i = 0; i < b; i++) {
        one_hot[i] <== a[i]-a[i+1];
        // assert((2**i <= in && in < 2**(i+1)) || one_hot[i]==1);
    }
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // TODO
    component msnzb = MSNZB(P+1);
    msnzb.in <== m;
    msnzb.skip_checks <== skip_checks;
    
    signal a[P+2],o[P+2];
    a[P+1] <== m;
    o[P+1] <== 1;
    // var o = 1;
    var ell = P;
    for (var i = P; i >= 0; i--) {
        o[i] <== (1-msnzb.one_hot[i])*o[i+1];
        a[i] <== a[i+1] + o[i]*a[i+1];
        ell -= o[i];
    }
    m_out <== a[0];
    e_out <== e + ell - p;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */
template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    // TODO
    component check_well_formedness[2];
    for (var i = 0; i < 2; i++) {
        check_well_formedness[i] = CheckWellFormedness(k, p);
        check_well_formedness[i].e <== e[i];
        check_well_formedness[i].m <== m[i];
    }

    signal e_left[2][p+2],mgn[2];
    for (var i = 0; i < 2; i++) {
        e_left[i][0] <== e[i];
        for(var j = 0; j < p+1; j++) {
            e_left[i][j+1] <== e_left[i][j]*2;
        }
        mgn[i] <== e_left[i][p+1] + m[i];
    }
    // log(mgn[0], mgn[1], p);
    component ls;
    ls = LessThan(2*p+2);
    ls.in[0] <== mgn[0];
    ls.in[1] <== mgn[1];
    

    component switcher[2];
    signal alpha_e, alpha_m, beta_e, beta_m;
    
    switcher[0] = Switcher();
    switcher[0].sel <== ls.out;
    switcher[0].L <== e[0];
    switcher[0].R <== e[1];
    alpha_e <== switcher[0].outL;
    beta_e <== switcher[0].outR;

    switcher[1] = Switcher();
    switcher[1].sel <== ls.out;
    switcher[1].L <== m[0];
    switcher[1].R <== m[1];
    alpha_m <== switcher[1].outL;
    beta_m <== switcher[1].outR;

    signal diff <== alpha_e - beta_e;

    signal m0,e0,m1,e1,m2,e2;

    component ls2 = LessThan(p); // p?
    ls2.in[0] <== p+1;
    ls2.in[1] <== diff;

    component is0 = IsZero();
    is0.in <== alpha_e;

    component or = OR();
    or.a <== ls2.out;
    or.b <== is0.out;

    component leftshift = LeftShift(p+2);
    leftshift.x <== alpha_m*(1-or.out);
    leftshift.shift <== diff*(1-or.out);
    leftshift.skip_checks <== or.out;

    // log(or.out);

    m0 <== leftshift.y + beta_m;
    e0 <== beta_e;

    component normalize = Normalize(k, p, 2*p+1);
    normalize.e <== e0*(1-or.out);
    normalize.m <== m0*(1-or.out);
    normalize.skip_checks <== or.out;
    e1 <== normalize.e_out;
    m1 <== normalize.m_out;

    component round_and_check = RoundAndCheck(k, p, 2*p+1);
    round_and_check.e <== e1*(1-or.out);
    round_and_check.m <== m1*(1-or.out);
    e2 <== round_and_check.e_out;
    m2 <== round_and_check.m_out;

    component if_e = IfThenElse();
    if_e.cond <== or.out;
    if_e.L <== alpha_e;
    if_e.R <== e2;
    e_out <== if_e.out;

    component if_m = IfThenElse();
    if_m.cond <== or.out;
    if_m.L <== alpha_m;
    if_m.R <== m2;
    m_out <== if_m.out;

}
