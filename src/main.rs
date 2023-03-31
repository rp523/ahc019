#![allow(unused_macros, unused_imports, dead_code)]
use std::any::TypeId;
use std::cmp::{max, min, Reverse};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::mem::swap;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign};

macro_rules! __debug_impl {
    ($x:expr) => {
        eprint!("{}={}  ", stringify!($x), &$x);
    };
    ($x:expr, $($y:expr),+) => (
        __debug_impl!($x);
        __debug_impl!($($y),+);
    );
}
macro_rules! __debug_line {
    () => {
        eprint!("L{}  ", line!());
    };
}
macro_rules! __debug_select {
    () => {
        eprintln!();
    };
    ($x:expr) => {
        __debug_line!();
        __debug_impl!($x);
        eprintln!();
    };
    ($x:expr, $($y:expr),+) => (
        __debug_line!();
        __debug_impl!($x);
        __debug_impl!($($y),+);
        eprintln!();
    );
}
macro_rules! debug {
    () => {
        if cfg!(debug_assertions) {
            __debug_select!();
        }
    };
    ($($xs:expr),+) => {
        if cfg!(debug_assertions) {
            __debug_select!($($xs),+);
        }
    };
}

pub trait Identity {
    fn identity() -> Self;
}
impl Identity for i32 {
    fn identity() -> Self {
        1_i32
    }
}
impl Identity for u32 {
    fn identity() -> Self {
        1_u32
    }
}
impl Identity for i64 {
    fn identity() -> Self {
        1_i64
    }
}
impl Identity for u64 {
    fn identity() -> Self {
        1_u64
    }
}
impl Identity for i128 {
    fn identity() -> Self {
        1_i128
    }
}
impl Identity for u128 {
    fn identity() -> Self {
        1_u128
    }
}
impl Identity for f64 {
    fn identity() -> Self {
        1_f64
    }
}
impl Identity for usize {
    fn identity() -> Self {
        1_usize
    }
}

mod change_min_max {
    pub trait ChangeMinMax<T> {
        fn chmin(&mut self, rhs: T) -> bool;
        fn chmax(&mut self, rhs: T) -> bool;
    }
    impl<T: PartialOrd + Copy> ChangeMinMax<T> for T {
        fn chmin(&mut self, rhs: T) -> bool {
            if *self > rhs {
                *self = rhs;
                true
            } else {
                false
            }
        }
        fn chmax(&mut self, rhs: T) -> bool {
            if *self < rhs {
                *self = rhs;
                true
            } else {
                false
            }
        }
    }
    impl<T: PartialOrd + Copy> ChangeMinMax<T> for Option<T> {
        fn chmin(&mut self, rhs: T) -> bool {
            if let Some(val) = *self {
                if val > rhs {
                    *self = Some(rhs);
                    true
                } else {
                    false
                }
            } else {
                *self = Some(rhs);
                true
            }
        }
        fn chmax(&mut self, rhs: T) -> bool {
            if let Some(val) = *self {
                if val < rhs {
                    *self = Some(rhs);
                    true
                } else {
                    false
                }
            } else {
                *self = Some(rhs);
                true
            }
        }
    }
}
use change_min_max::ChangeMinMax;

mod gcd {
    use std::cmp::{PartialEq, PartialOrd};
    use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign};
    pub fn gcd<T: Copy + Sub<Output = T> + Rem<Output = T> + PartialEq>(a: T, b: T) -> T {
        #[allow(clippy::eq_op)]
        let zero = a - a;
        if b == zero {
            a
        } else {
            gcd(b, a % b)
        }
    }
    // returns (p, q) s. t. ap + bq = gcd(a, b)
    pub fn ext_gcd<
        T: Eq
            + Copy
            + Sub<Output = T>
            + SubAssign
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>,
    >(
        a: T,
        b: T,
    ) -> (T, T) {
        #[allow(clippy::eq_op)]
        let zero = b - b;
        #[allow(clippy::eq_op)]
        let one = b / b;
        if a == zero {
            return (zero, one);
        }
        // (b % a) * x + a * y = gcd(a, b)
        // b % a = b - (b / a) * a
        // ->
        // (b - (b / a) * a) * x + a * y = gcd(a, b)
        // a * (y - (b / a) * x) + b * x = gcd(a, b)
        let (x, y) = ext_gcd(b % a, a);
        (y - b / a * x, x)
    }
    // Chinese Remainder Theorem
    // when exists, returns (lcm(m1, m2), x) s.t. x = r1 (mod  m1) and x = r2 (mod m2)
    fn chinese_rem_elem2<
        T: Eq
            + Copy
            + Neg<Output = T>
            + PartialOrd
            + Add<Output = T>
            + AddAssign
            + Sub<Output = T>
            + SubAssign
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + RemAssign,
    >(
        m1: T,
        r1: T,
        m2: T,
        r2: T,
    ) -> Option<(T, T)> {
        #[allow(clippy::eq_op)]
        let zero = m1 - m1;
        #[allow(clippy::eq_op)]
        let one = m1 / m1;
        let (p, _q) = ext_gcd(m1, m2);
        let g = gcd(m1, m2);
        if (r2 - r1) % g != zero {
            None
        } else {
            let lcm = m1 * (m2 / g);
            let mut r = r1 + m1 * ((r2 - r1) / g) * p;
            if r < zero {
                let dv = (-r + lcm - one) / lcm;
                r += dv * lcm;
            }
            r %= lcm;
            Some((lcm, r))
        }
    }
    // Chinese Remainder Theorem
    // when exists, returns (lcm(mods), x) s.t. x = r_i (mod  m_i) for all i.
    pub fn chinese_rem<
        T: Eq
            + Copy
            + Neg<Output = T>
            + PartialOrd
            + Add<Output = T>
            + AddAssign
            + Sub<Output = T>
            + SubAssign
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + RemAssign,
    >(
        mods: &[T],
        rems: &[T],
    ) -> Option<(T, T)> {
        debug_assert!(mods.len() == rems.len());
        #[allow(clippy::eq_op)]
        let zero = mods[0] - mods[0];
        #[allow(clippy::eq_op)]
        let one = mods[0] / mods[0];
        let mut lcm = one;
        let mut rem = zero;
        for (m, r) in mods.iter().copied().zip(rems.iter().copied()) {
            if let Some((nlcm, nrem)) = chinese_rem_elem2(lcm, rem, m, r) {
                lcm = nlcm;
                rem = nrem;
            } else {
                return None;
            }
        }
        Some((lcm, rem))
    }
}
use gcd::*;

fn factorial_impl<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T>,
>(
    p: usize,
    memo: &mut Vec<usize>,
    update_op: fn(T, T) -> T,
) -> T {
    while memo.len() < 2_usize {
        memo.push(1_usize);
    }
    while memo.len() <= p + 1 {
        let last_val: T = T::from(*memo.last().unwrap());
        memo.push(update_op(last_val, T::from(memo.len())).into());
    }
    T::from(memo[p])
}

fn factorial<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    p: usize,
) -> T {
    static mut MEMO: Vec<usize> = Vec::<usize>::new();
    unsafe { factorial_impl(p, &mut MEMO, |x: T, y: T| x * y) }
}

fn factorial_inv<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    p: usize,
) -> T {
    static mut MEMO: Vec<usize> = Vec::<usize>::new();
    unsafe { factorial_impl(p, &mut MEMO, |x: T, y: T| x / y) }
}

fn combination<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    if k == 0 {
        return T::from(1_usize);
    } else if k == 1 {
        return T::from(n);
    } else if k == 2 {
        return (T::from(n) * T::from(n - 1)) / T::from(2);
    }

    if TypeId::of::<mint>() == TypeId::of::<T>() {
        factorial::<T>(n) * factorial_inv::<T>(k) * factorial_inv::<T>(n - k)
    } else {
        factorial::<T>(n) / (factorial::<T>(k) * factorial::<T>(n - k))
    }
}

fn permutation<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    if k == 0 {
        return T::from(1_usize);
    } else if k == 1 {
        return T::from(n);
    } else if k == 2 {
        return T::from(n) * T::from(n - 1);
    }

    if TypeId::of::<mint>() == TypeId::of::<T>() {
        factorial::<T>(n) * factorial_inv::<T>(n - k)
    } else {
        factorial::<T>(n) / factorial::<T>(n - k)
    }
}

mod union_find {
    #[derive(Debug, Clone)]
    pub struct UnionFind {
        pub graph: Vec<Vec<usize>>,
        parents: Vec<usize>,
        grp_sz: Vec<usize>,
        grp_num: usize,
    }

    impl UnionFind {
        pub fn new(sz: usize) -> Self {
            Self {
                graph: vec![vec![]; sz],
                parents: (0..sz).collect::<Vec<usize>>(),
                grp_sz: vec![1; sz],
                grp_num: sz,
            }
        }
        pub fn root(&mut self, v: usize) -> usize {
            if v == self.parents[v] {
                v
            } else {
                self.parents[v] = self.root(self.parents[v]);
                self.parents[v]
            }
        }
        pub fn same(&mut self, a: usize, b: usize) -> bool {
            self.root(a) == self.root(b)
        }
        pub fn unite(&mut self, into: usize, from: usize) {
            self.graph[into].push(from);
            self.graph[from].push(into);
            let r_into = self.root(into);
            let r_from = self.root(from);
            if r_into != r_from {
                self.parents[r_from] = r_into;
                self.grp_sz[r_into] += self.grp_sz[r_from];
                self.grp_sz[r_from] = 0;
                self.grp_num -= 1;
            }
        }
        pub fn group_num(&self) -> usize {
            self.grp_num
        }
        pub fn group_size(&mut self, a: usize) -> usize {
            let ra = self.root(a);
            self.grp_sz[ra]
        }
    }
}
use union_find::UnionFind;

mod segment_tree {
    use std::ops::{Add, Sub};
    #[derive(Debug, Clone)]
    pub struct SegmentTree<T> {
        n2: usize,   // implemented leaf num (2^n)
        neff: usize, // effective vector length
        dat: Vec<T>,
        pair_op: fn(T, T) -> T,
    }
    impl<T: Copy> SegmentTree<T> {
        pub fn new(n: usize, pair_op: fn(T, T) -> T, ini_val: T) -> Self {
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut s = Self {
                n2,
                neff: n,
                pair_op,
                dat: vec![ini_val; 2 * n2 - 1],
            };

            for i in 0..n {
                s.set(i, ini_val);
            }
            s
        }
        pub fn from(pair_op: fn(T, T) -> T, ini_values: Vec<T>) -> Self {
            let n = ini_values.len();
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut st = Self {
                n2,
                neff: n,
                pair_op,
                dat: vec![ini_values[0]; 2 * n2 - 1],
            };

            for (i, ini_val) in ini_values.iter().enumerate() {
                st.set(i, *ini_val);
            }
            st
        }
        pub fn set(&mut self, mut pos: usize, val: T) {
            pos += self.n2 - 1;
            self.dat[pos] = val;
            while pos > 0 {
                pos = (pos - 1) / 2; // parent
                self.dat[pos] = (self.pair_op)(self.dat[pos * 2 + 1], self.dat[pos * 2 + 2]);
            }
        }
        pub fn get(&self, pos: usize) -> T {
            self.dat[pos + self.n2 - 1]
        }
        // get query value of [a, b]
        pub fn query(&self, a: usize, b: usize) -> T {
            self.query_sub(a, b + 1, 0, 0, self.n2)
        }
        // get query value of [a, b)
        fn query_sub(&self, a: usize, b: usize, node: usize, node_l: usize, node_r: usize) -> T {
            if (node_r <= a) || (b <= node_l) {
                panic!("invalid query range, ({a}, {b})");
            } else if (a <= node_l) && (node_r <= b) {
                // this not is covered by given interval.
                self.dat[node]
            } else if a < (node_l + node_r) / 2 {
                let vl = self.query_sub(a, b, node * 2 + 1, node_l, (node_l + node_r) / 2);
                if (node_l + node_r) / 2 < b {
                    let vr = self.query_sub(a, b, node * 2 + 2, (node_l + node_r) / 2, node_r);
                    (self.pair_op)(vl, vr)
                } else {
                    vl
                }
            } else if (node_l + node_r) / 2 < b {
                self.query_sub(a, b, node * 2 + 2, (node_l + node_r) / 2, node_r)
            } else {
                panic!("invalid query range, ({a}, {b})");
            }
        }
    }
    impl<T: Copy + Add<Output = T> + Sub<Output = T>> SegmentTree<T> {
        pub fn add(&mut self, pos: usize, add_val: T) {
            self.set(pos, self.get(pos) + add_val);
        }
        pub fn sub(&mut self, pos: usize, sub_val: T) {
            self.set(pos, self.get(pos) - sub_val);
        }
    }
}
use segment_tree::SegmentTree;

mod lazy_segment_tree {
    #[derive(Clone)]
    pub struct LazySegmentTree<X, M> {
        // https://algo-logic.info/segment-tree/#toc_id_3
        n2: usize,                    // num of node(integer power of 2)
        pair_op: fn(X, X) -> X,       // node_val x node_val -> node_val
        update_op: fn(X, M) -> X,     // node_val x update_val -> node
        update_concat: fn(M, M) -> M, // update_val x update_val -> update_val
        dat: Vec<X>,                  // node values
        lazy_ops: Vec<Option<M>>,     // reserved operations
        built: bool,
    }
    impl<X: Copy, M: Copy> LazySegmentTree<X, M> {
        pub fn new(
            n: usize,
            pair_op: fn(X, X) -> X,
            update_op: fn(X, M) -> X,
            update_concat: fn(M, M) -> M,
            ini_val: X,
        ) -> Self {
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut ret = Self {
                n2,
                pair_op,
                update_op,
                update_concat,
                dat: vec![ini_val; n * 4],
                lazy_ops: vec![None; n * 4],
                built: false,
            };
            ret.init_all(ini_val);
            ret
        }
        pub fn from(
            pair_op: fn(X, X) -> X,
            update_op: fn(X, M) -> X,
            update_concat: fn(M, M) -> M,
            init_vals: &[X],
        ) -> Self {
            let n = init_vals.len();
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut ret = Self {
                n2,
                pair_op,
                update_op,
                update_concat,
                dat: vec![init_vals[0]; n * 4],
                lazy_ops: vec![None; n * 4],
                built: false,
            };
            for (i, init_val) in init_vals.iter().enumerate() {
                ret.set(i, *init_val);
            }
            ret
        }
        pub fn query(&mut self, a: usize, b: usize) -> X // closed interval
        {
            self.query_sub(a, b + 1, 0, 0, self.n2) // half_open interval
        }
        pub fn reserve(&mut self, a: usize, b: usize, m: M) // closed interval
        {
            self.reserve_sub(a, b + 1, m, 0, 0, self.n2); // half_open interval
        }
        pub fn set(&mut self, i: usize, val: X) {
            self.dat[i + self.n2 - 1] = val;
        }
        fn init_all(&mut self, ini_val: X) {
            for i in 0..self.n2 {
                self.set(i, ini_val);
            }
        }
        fn build(&mut self) {
            for k in (0..self.n2).rev().skip(1) {
                self.dat[k] = (self.pair_op)(self.dat[2 * k + 1], self.dat[2 * k + 2]);
            }
        }
        fn lazy_eval(&mut self, node: usize) {
            if !self.built {
                self.build();
                self.built = true;
            }
            if let Some(lazy_val) = self.lazy_ops[node] {
                if node < self.n2 - 1 {
                    // if the target node is not a terminal one, propagate to its' children.
                    for d in 1..=2_usize {
                        let nc = node * 2 + d;
                        if let Some(nc_lazy_val) = self.lazy_ops[nc] {
                            self.lazy_ops[nc] = Some((self.update_concat)(nc_lazy_val, lazy_val));
                        } else {
                            self.lazy_ops[nc] = Some(lazy_val);
                        }
                    }
                }
                // update the target node
                self.dat[node] = (self.update_op)(self.dat[node], lazy_val);
                self.lazy_ops[node] = None;
            }
        }
        fn reserve_sub(
            &mut self,
            a: usize,
            b: usize,
            m: M,
            node: usize,
            node_l: usize,
            node_r: usize,
        ) {
            self.lazy_eval(node);
            if (a <= node_l) && (node_r <= b) {
                // this node is inside the query range.
                if let Some(lazy_val) = self.lazy_ops[node] {
                    self.lazy_ops[node] = Some((self.update_concat)(lazy_val, m));
                } else {
                    self.lazy_ops[node] = Some(m);
                }
                self.lazy_eval(node);
            } else if (node_r > a) && (b > node_l) {
                // this node and query range overlap partly.
                self.reserve_sub(a, b, m, node * 2 + 1, node_l, (node_l + node_r) / 2); // 左の子
                self.reserve_sub(a, b, m, node * 2 + 2, (node_l + node_r) / 2, node_r); // 右の子
                self.dat[node] = (self.pair_op)(self.dat[node * 2 + 1], self.dat[node * 2 + 2]);
            }
        }
        fn query_sub(
            &mut self,
            a: usize,
            b: usize,
            node: usize,
            node_l: usize,
            node_r: usize,
        ) -> X {
            self.lazy_eval(node);
            if (a <= node_l) && (node_r <= b) {
                // this node is inside the query range.
                self.dat[node]
            } else if (node_r > a) && (b > node_l) {
                // this node and query range overlap partly.
                let n0 = node * 2 + 1;
                let l0 = node_l;
                let r0 = (node_l + node_r) / 2;
                let n1 = node * 2 + 2;
                let l1 = (node_l + node_r) / 2;
                let r1 = node_r;
                if (a < r0) && (l0 < b) {
                    if (a < r1) && (l1 < b) {
                        (self.pair_op)(
                            self.query_sub(a, b, n0, l0, r0),
                            self.query_sub(a, b, n1, l1, r1),
                        )
                    } else {
                        self.query_sub(a, b, n0, l0, r0)
                    }
                } else if (a < r1) && (l1 < b) {
                    self.query_sub(a, b, n1, l1, r1)
                } else {
                    panic!("invalid arg range {}, {}", a, b);
                }
            } else {
                panic!(
                    "this node and query range have no common area, {}, {}",
                    a, b
                );
            }
        }
    }
}
use lazy_segment_tree::LazySegmentTree;

mod modint {
    use crate::gcd::ext_gcd;
    use crate::Identity;
    use std::fmt;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, Sub, SubAssign};
    static mut MOD: i64 = 2;

    #[derive(Clone, Copy, Eq, Hash, PartialEq)]
    pub struct ModInt {
        x: i64,
    }
    impl ModInt {
        pub fn set_mod(val: i64) {
            unsafe {
                MOD = val;
            }
        }
        pub fn get_mod() -> i64 {
            unsafe { MOD }
        }
        pub fn val(&self) -> i64 {
            self.x
        }
        fn new(mut sig: i64) -> Self {
            if sig < 0 {
                let ab = (-sig + Self::get_mod() - 1) / Self::get_mod();
                sig += ab * Self::get_mod();
                debug_assert!(sig >= 0);
            }
            Self {
                x: sig % Self::get_mod(),
            }
        }
        fn inverse(&self) -> Self {
            // x * inv_x + M * _ = 1 (mod M)
            Self::new(ext_gcd(self.x, Self::get_mod()).0)

            // [Fermat's little theorem]
            // if p is prime, for any integer a, a^p = a (mod p)
            // especially when a and b is coprime, a^(p-1) = 1 (mod p).
            // -> inverse of a is a^(p-2).

            //let mut ret = Self { x: 1 };
            //let mut mul: Self = *self;
            //let mut p = Self::get_mod() - 2;
            //while p > 0 {
            //    if p & 1 != 0 {
            //        ret *= mul;
            //    }
            //    p >>= 1;
            //    mul *= mul;
            //}
            //ret
        }
        pub fn pow(self, mut p: usize) -> Self {
            let mut ret = ModInt::from(1);
            let mut mul = self;
            while p > 0 {
                if p & 1 != 0 {
                    ret *= mul;
                }
                p >>= 1;
                mul *= mul;
            }
            ret
        }
    }
    impl Identity for ModInt {
        fn identity() -> Self {
            Self { x: 1 }
        }
    }
    impl AddAssign<Self> for ModInt {
        fn add_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x + rhs.x);
        }
    }
    impl AddAssign<i64> for ModInt {
        fn add_assign(&mut self, rhs: i64) {
            *self = ModInt::new(self.x + rhs);
        }
    }
    impl AddAssign<i32> for ModInt {
        fn add_assign(&mut self, rhs: i32) {
            *self = ModInt::new(self.x + rhs as i64);
        }
    }
    impl AddAssign<usize> for ModInt {
        fn add_assign(&mut self, rhs: usize) {
            *self = ModInt::new(self.x + rhs as i64);
        }
    }
    impl Add<ModInt> for ModInt {
        type Output = ModInt;
        fn add(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x + rhs.x)
        }
    }
    impl Add<i64> for ModInt {
        type Output = ModInt;
        fn add(self, rhs: i64) -> Self::Output {
            ModInt::new(self.x + rhs)
        }
    }
    impl Add<i32> for ModInt {
        type Output = ModInt;
        fn add(self, rhs: i32) -> Self::Output {
            ModInt::new(self.x + rhs as i64)
        }
    }
    impl Add<usize> for ModInt {
        type Output = ModInt;
        fn add(self, rhs: usize) -> Self::Output {
            ModInt::new(self.x + rhs as i64)
        }
    }
    impl Add<ModInt> for i64 {
        type Output = ModInt;
        fn add(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self + rhs.x)
        }
    }
    impl Add<ModInt> for i32 {
        type Output = ModInt;
        fn add(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 + rhs.x)
        }
    }
    impl Add<ModInt> for usize {
        type Output = ModInt;
        fn add(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 + rhs.x)
        }
    }
    impl SubAssign<Self> for ModInt {
        fn sub_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x - rhs.x);
        }
    }
    impl SubAssign<i64> for ModInt {
        fn sub_assign(&mut self, rhs: i64) {
            *self = ModInt::new(self.x - rhs);
        }
    }
    impl SubAssign<i32> for ModInt {
        fn sub_assign(&mut self, rhs: i32) {
            *self = ModInt::new(self.x - rhs as i64);
        }
    }
    impl SubAssign<usize> for ModInt {
        fn sub_assign(&mut self, rhs: usize) {
            *self = ModInt::new(self.x - rhs as i64);
        }
    }
    impl Sub<ModInt> for ModInt {
        type Output = ModInt;
        fn sub(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x - rhs.x)
        }
    }
    impl Sub<i64> for ModInt {
        type Output = ModInt;
        fn sub(self, rhs: i64) -> Self::Output {
            ModInt::new(self.x - rhs)
        }
    }
    impl Sub<i32> for ModInt {
        type Output = ModInt;
        fn sub(self, rhs: i32) -> Self::Output {
            ModInt::new(self.x - rhs as i64)
        }
    }
    impl Sub<usize> for ModInt {
        type Output = ModInt;
        fn sub(self, rhs: usize) -> Self::Output {
            ModInt::new(self.x - rhs as i64)
        }
    }
    impl Sub<ModInt> for i64 {
        type Output = ModInt;
        fn sub(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self - rhs.x)
        }
    }
    impl Sub<ModInt> for i32 {
        type Output = ModInt;
        fn sub(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 - rhs.x)
        }
    }
    impl Sub<ModInt> for usize {
        type Output = ModInt;
        fn sub(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 - rhs.x)
        }
    }
    impl MulAssign<Self> for ModInt {
        fn mul_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x * rhs.x);
        }
    }
    impl MulAssign<i64> for ModInt {
        fn mul_assign(&mut self, rhs: i64) {
            *self = ModInt::new(self.x * rhs);
        }
    }
    impl MulAssign<i32> for ModInt {
        fn mul_assign(&mut self, rhs: i32) {
            *self = ModInt::new(self.x * rhs as i64);
        }
    }
    impl MulAssign<usize> for ModInt {
        fn mul_assign(&mut self, rhs: usize) {
            *self = ModInt::new(self.x * rhs as i64);
        }
    }
    impl Mul<ModInt> for ModInt {
        type Output = ModInt;
        fn mul(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x * rhs.x)
        }
    }
    impl Mul<i64> for ModInt {
        type Output = ModInt;
        fn mul(self, rhs: i64) -> Self::Output {
            ModInt::new(self.x * rhs)
        }
    }
    impl Mul<i32> for ModInt {
        type Output = ModInt;
        fn mul(self, rhs: i32) -> Self::Output {
            ModInt::new(self.x * rhs as i64)
        }
    }
    impl Mul<usize> for ModInt {
        type Output = ModInt;
        fn mul(self, rhs: usize) -> Self::Output {
            ModInt::new(self.x * rhs as i64)
        }
    }
    impl Mul<ModInt> for i64 {
        type Output = ModInt;
        fn mul(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self * rhs.x)
        }
    }
    impl Mul<ModInt> for i32 {
        type Output = ModInt;
        fn mul(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 * rhs.x)
        }
    }
    impl Mul<ModInt> for usize {
        type Output = ModInt;
        fn mul(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 * rhs.x)
        }
    }
    impl DivAssign<Self> for ModInt {
        fn div_assign(&mut self, rhs: Self) {
            *self = *self / rhs;
        }
    }
    impl DivAssign<i64> for ModInt {
        fn div_assign(&mut self, rhs: i64) {
            *self = *self / ModInt::new(rhs);
        }
    }
    impl DivAssign<i32> for ModInt {
        fn div_assign(&mut self, rhs: i32) {
            *self = *self / ModInt::new(rhs as i64);
        }
    }
    impl DivAssign<usize> for ModInt {
        fn div_assign(&mut self, rhs: usize) {
            *self = *self / ModInt::new(rhs as i64);
        }
    }
    impl Div<ModInt> for ModInt {
        type Output = ModInt;
        fn div(self, rhs: Self) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * rhs.inverse().x)
        }
    }
    impl Div<i64> for ModInt {
        type Output = ModInt;
        fn div(self, rhs: i64) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * ModInt::new(rhs).inverse().x)
        }
    }
    impl Div<i32> for ModInt {
        type Output = ModInt;
        fn div(self, rhs: i32) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * ModInt::new(rhs as i64).inverse().x)
        }
    }
    impl Div<usize> for ModInt {
        type Output = ModInt;
        fn div(self, rhs: usize) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * ModInt::new(rhs as i64).inverse().x)
        }
    }
    impl Div<ModInt> for i64 {
        type Output = ModInt;
        fn div(self, rhs: ModInt) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self * rhs.inverse().x)
        }
    }
    impl Div<ModInt> for i32 {
        type Output = ModInt;
        fn div(self, rhs: ModInt) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self as i64 * rhs.inverse().x)
        }
    }
    impl Div<ModInt> for usize {
        type Output = ModInt;
        fn div(self, rhs: ModInt) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self as i64 * rhs.inverse().x)
        }
    }
    impl From<usize> for ModInt {
        fn from(x: usize) -> Self {
            ModInt::new(x as i64)
        }
    }
    impl From<i64> for ModInt {
        fn from(x: i64) -> Self {
            ModInt::new(x)
        }
    }
    impl From<i32> for ModInt {
        fn from(x: i32) -> Self {
            ModInt::new(x as i64)
        }
    }
    impl std::str::FromStr for ModInt {
        type Err = std::num::ParseIntError;
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            match s.parse::<i64>() {
                Ok(x) => Ok(ModInt::from(x)),
                Err(e) => Err(e),
            }
        }
    }
    impl std::iter::Sum for ModInt {
        fn sum<I: Iterator<Item = ModInt>>(iter: I) -> Self {
            let mut ret = ModInt::new(0);
            for v in iter {
                ret += v;
            }
            ret
        }
    }
    #[allow(clippy::from_over_into)]
    impl Into<usize> for ModInt {
        fn into(self) -> usize {
            self.x as usize
        }
    }
    impl fmt::Display for ModInt {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.x)
        }
    }
    impl fmt::Debug for ModInt {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.x)
        }
    }
}
use modint::ModInt as mint;

fn precalc_power(base: i64, n: usize) -> Vec<mint> {
    let mut ret = vec![mint::from(1); n + 1];
    for p in 1..=n {
        ret[p] = ret[p - 1] * base;
    }
    ret
}

fn precalc_invpower(base: i64, n: usize) -> Vec<mint> {
    let mut ret = vec![mint::from(1); n + 1];
    let inv_base = mint::from(1) / base;
    for p in 1..=n {
        ret[p] = ret[p - 1] * inv_base;
    }
    ret
}

pub trait IntegerOperation {
    fn into_primes(self) -> BTreeMap<Self, usize>
    where
        Self: Sized;
    fn into_divisors(self) -> Vec<Self>
    where
        Self: Sized;
    fn squared_length(&self, rhs: Self) -> Self;
}
impl<
        T: Copy
            + Ord
            + AddAssign
            + SubAssign
            + MulAssign
            + DivAssign
            + Add<Output = T>
            + Sub<Output = T>
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>,
    > IntegerOperation for T
{
    fn into_primes(self) -> BTreeMap<T, usize> // O(N^0.5 x logN)
    {
        #[allow(clippy::eq_op)]
        let zero = self - self;
        if self == zero {
            panic!("Zero has no divisors.");
        }
        #[allow(clippy::eq_op)]
        let one = self / self;
        let two = one + one;
        let three = two + one;
        let mut n = self;
        let mut ans = BTreeMap::new();
        while n % two == zero {
            *ans.entry(two).or_insert(0) += 1;
            n /= two;
        }
        {
            let mut i = three;
            while i * i <= n {
                while n % i == zero {
                    *ans.entry(i).or_insert(0) += 1;
                    n /= i;
                }
                i += two;
            }
        }
        if n != one {
            *ans.entry(n).or_insert(0) += 1;
        }
        ans
    }
    fn into_divisors(self) -> Vec<T> // O(N^0.5)
    {
        #[allow(clippy::eq_op)]
        let zero = self - self;
        if self == zero {
            panic!("Zero has no primes.");
        }
        #[allow(clippy::eq_op)]
        let one = self / self;
        let n = self;
        let mut ret: Vec<T> = Vec::new();
        {
            let mut i = one;
            while i * i <= n {
                if n % i == zero {
                    ret.push(i);
                    if i * i != n {
                        ret.push(n / i);
                    }
                }
                i += one;
            }
        }
        ret.sort();
        ret
    }
    fn squared_length(&self, rhs: Self) -> Self {
        *self * *self + rhs * rhs
    }
}

pub trait CoordinateCompress<T> {
    fn compress_encoder(&self) -> HashMap<T, usize>;
    fn compress_decoder(&self) -> Vec<T>;
    fn compress(self) -> Vec<usize>;
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for Vec<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = BTreeSet::new();
        for &x in self.iter() {
            dict.insert(x);
        }
        let mut ret = HashMap::new();
        for (i, value) in dict.into_iter().enumerate() {
            ret.insert(value, i);
        }
        ret
    }
    fn compress_decoder(&self) -> Vec<T> {
        let mut keys = BTreeSet::<T>::new();
        for &x in self.iter() {
            keys.insert(x);
        }
        keys.into_iter().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        let dict = self.compress_encoder();
        self.into_iter().map(|x| dict[&x]).collect::<Vec<usize>>()
    }
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for BTreeSet<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = HashMap::new();
        for (i, &key) in self.iter().enumerate() {
            dict.insert(key, i);
        }
        dict
    }
    fn compress_decoder(&self) -> Vec<T> {
        self.iter().copied().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        (0..self.len()).collect::<Vec<usize>>()
    }
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for HashSet<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = BTreeSet::new();
        for &x in self.iter() {
            dict.insert(x);
        }
        let mut ret = HashMap::new();
        for (i, value) in dict.into_iter().enumerate() {
            ret.insert(value, i);
        }
        ret
    }
    fn compress_decoder(&self) -> Vec<T> {
        let mut keys = BTreeSet::<T>::new();
        for &x in self.iter() {
            keys.insert(x);
        }
        keys.into_iter().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        let dict = self.compress_encoder();
        self.into_iter().map(|x| dict[&x]).collect::<Vec<usize>>()
    }
}

mod xor_shift_64 {
    pub struct XorShift64(u64);
    impl XorShift64 {
        pub fn new() -> Self {
            XorShift64(88172645463325252_u64)
        }
        pub fn next_f64(&mut self) -> f64 {
            self.0 = self.0 ^ (self.0 << 7);
            self.0 = self.0 ^ (self.0 >> 9);
            self.0 as f64 * 5.421_010_862_427_522e-20
        }
        pub fn next_u64(&mut self) -> u64 {
            self.0 = self.0 ^ (self.0 << 7);
            self.0 = self.0 ^ (self.0 >> 9);
            self.0
        }
        pub fn next_usize(&mut self) -> usize {
            self.next_u64() as usize
        }
        pub fn next_permutation(&mut self, n: usize) -> Vec<usize> {
            let mut ret = (0..n).collect::<Vec<_>>();
            for _ in 0..(2 * n) {
                let i = self.next_usize() % (n - 1);
                let j = i + 1 + self.next_usize() % (n - (i + 1));
                ret.swap(i, j);
            }
            ret
        }
    }
}
use xor_shift_64::XorShift64;

mod rooted_tree {
    use std::mem::swap;

    use crate::union_find::UnionFind;
    pub struct RootedTree {
        n: usize,
        doubling_bit_width: usize,
        root: usize,
        rise_tbl: Vec<Vec<Option<usize>>>,
        dist: Vec<Option<i64>>,
        step: Vec<Option<usize>>,
        pub graph: Vec<Vec<(i64, usize)>>,
        edge_cnt: usize,
        uf: UnionFind,
    }
    impl RootedTree {
        pub fn new(n: usize, root: usize) -> RootedTree {
            let mut doubling_bit_width = 1;
            while (1 << doubling_bit_width) < n {
                doubling_bit_width += 1;
            }
            RootedTree {
                n,
                doubling_bit_width,
                root,
                rise_tbl: vec![vec![None; n]; doubling_bit_width],
                dist: vec![None; n],
                step: vec![None; n],
                graph: vec![vec![]; n],
                edge_cnt: 0,
                uf: UnionFind::new(n),
            }
        }
        pub fn unite(&mut self, a: usize, b: usize) {
            self.unite_with_distance(a, b, 1);
        }
        pub fn unite_with_distance(&mut self, a: usize, b: usize, delta: i64) {
            self.graph[a].push((delta, b));
            self.graph[b].push((delta, a));
            self.edge_cnt += 1;
            self.uf.unite(a, b);
            if self.edge_cnt >= self.n - 1 {
                if self.uf.group_num() != 1 {
                    panic!("nodes are NOT connected into one union.")
                }
                self.analyze(self.root);
            }
        }
        pub fn stepback(&self, from: usize, step: usize) -> usize {
            let mut v = from;
            for d in (0..self.doubling_bit_width - 1).rev() {
                if ((step >> d) & 1) != 0 {
                    v = self.rise_tbl[d][v].unwrap();
                }
            }
            v
        }
        fn dfs(
            v: usize,
            pre: Option<usize>,
            graph: &Vec<Vec<(i64, usize)>>,
            dist: &mut Vec<Option<i64>>,
            step: &mut Vec<Option<usize>>,
            rise_tbl: &mut Vec<Vec<Option<usize>>>,
        ) {
            for (delta, nv) in graph[v].iter() {
                if let Some(pre) = pre {
                    if *nv == pre {
                        continue;
                    }
                }
                if dist[*nv].is_none() {
                    dist[*nv] = Some(dist[v].unwrap() + *delta);
                    step[*nv] = Some(step[v].unwrap() + 1);
                    rise_tbl[0][*nv] = Some(v);
                    Self::dfs(*nv, Some(v), graph, dist, step, rise_tbl);
                }
            }
        }
        fn analyze(&mut self, root: usize) {
            self.dist[root] = Some(0);
            self.step[root] = Some(0);
            self.rise_tbl[0][root] = Some(root);
            Self::dfs(
                root,
                None,
                &self.graph,
                &mut self.dist,
                &mut self.step,
                &mut self.rise_tbl,
            );
            // doubling
            for d in (0..self.doubling_bit_width).skip(1) {
                for v in 0_usize..self.n {
                    self.rise_tbl[d][v] = self.rise_tbl[d - 1][self.rise_tbl[d - 1][v].unwrap()];
                }
            }
        }
        pub fn lca(&self, mut a: usize, mut b: usize) -> usize {
            if self.step[a] > self.step[b] {
                swap(&mut a, &mut b);
            }
            assert!(self.step[a] <= self.step[b]);
            // bring up the deeper one to the same level of the shallower one.
            for d in (0..self.doubling_bit_width).rev() {
                let rise_v = self.rise_tbl[d][b].unwrap();
                if self.step[rise_v] >= self.step[a] {
                    b = rise_v;
                }
            }
            assert!(self.step[a] == self.step[b]);
            if a != b {
                // simultaneously rise to the previous level of LCA.
                for d in (0..self.doubling_bit_width).rev() {
                    if self.rise_tbl[d][a] != self.rise_tbl[d][b] {
                        a = self.rise_tbl[d][a].unwrap();
                        b = self.rise_tbl[d][b].unwrap();
                    }
                }
                // 1-step higher level is LCA.
                a = self.rise_tbl[0][a].unwrap();
                b = self.rise_tbl[0][b].unwrap();
            }
            assert!(a == b);
            a
        }
        pub fn distance(&self, a: usize, b: usize) -> i64 {
            let lca_v = self.lca(a, b);
            self.dist[a].unwrap() + self.dist[b].unwrap() - 2 * self.dist[lca_v].unwrap()
        }
    }
}
use rooted_tree::RootedTree;

mod btree_map_binary_search {
    use std::collections::BTreeMap;
    use std::ops::Bound::{Excluded, Included, Unbounded};
    pub trait BTreeMapBinarySearch<K, V> {
        fn greater_equal(&self, key: &K) -> Option<(&K, &V)>;
        fn greater_than(&self, key: &K) -> Option<(&K, &V)>;
        fn less_equal(&self, key: &K) -> Option<(&K, &V)>;
        fn less_than(&self, key: &K) -> Option<(&K, &V)>;
    }
    impl<K: Ord, V> BTreeMapBinarySearch<K, V> for BTreeMap<K, V> {
        fn greater_equal(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Included(key), Unbounded)).next()
        }
        fn greater_than(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Excluded(key), Unbounded)).next()
        }
        fn less_equal(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Unbounded, Included(key))).next_back()
        }
        fn less_than(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Unbounded, Excluded(key))).next_back()
        }
    }
}
use btree_map_binary_search::BTreeMapBinarySearch;

mod btree_set_binary_search {
    use std::collections::BTreeSet;
    use std::ops::Bound::{Excluded, Included, Unbounded};
    pub trait BTreeSetBinarySearch<T> {
        fn greater_equal(&self, key: &T) -> Option<&T>;
        fn greater_than(&self, key: &T) -> Option<&T>;
        fn less_equal(&self, key: &T) -> Option<&T>;
        fn less_than(&self, key: &T) -> Option<&T>;
    }
    impl<T: Ord> BTreeSetBinarySearch<T> for BTreeSet<T> {
        fn greater_equal(&self, key: &T) -> Option<&T> {
            self.range((Included(key), Unbounded)).next()
        }
        fn greater_than(&self, key: &T) -> Option<&T> {
            self.range((Excluded(key), Unbounded)).next()
        }
        fn less_equal(&self, key: &T) -> Option<&T> {
            self.range((Unbounded, Included(key))).next_back()
        }
        fn less_than(&self, key: &T) -> Option<&T> {
            self.range((Unbounded, Excluded(key))).next_back()
        }
    }
}
use btree_set_binary_search::BTreeSetBinarySearch;

mod sort_vec_binary_search {
    static mut VEC_IS_SORTED_ONCE: bool = false;
    #[allow(clippy::type_complexity)]
    fn sorted_binary_search<'a, T: PartialOrd>(
        vec: &'a Vec<T>,
        key: &T,
        earlier: fn(&T, &T) -> bool,
    ) -> (Option<(usize, &'a T)>, Option<(usize, &'a T)>) {
        unsafe {
            if !VEC_IS_SORTED_ONCE {
                for i in 1..vec.len() {
                    assert!(vec[i - 1] <= vec[i]);
                }
                VEC_IS_SORTED_ONCE = true;
            }
        }
        if vec.is_empty() {
            return (None, None);
        }

        if !earlier(&vec[0], key) {
            (None, Some((0, &vec[0])))
        } else if earlier(vec.last().unwrap(), key) {
            (Some((vec.len() - 1, &vec[vec.len() - 1])), None)
        } else {
            let mut l = 0;
            let mut r = vec.len() - 1;
            while r - l > 1 {
                let m = (l + r) / 2;
                if earlier(&vec[m], key) {
                    l = m;
                } else {
                    r = m;
                }
            }
            (Some((l, &vec[l])), Some((r, &vec[r])))
        }
    }
    pub trait SortVecBinarySearch<T> {
        #[allow(clippy::type_complexity)]
        fn greater_equal(&self, key: &T) -> Option<(usize, &T)>;
        fn greater_than(&self, key: &T) -> Option<(usize, &T)>;
        fn less_equal(&self, key: &T) -> Option<(usize, &T)>;
        fn less_than(&self, key: &T) -> Option<(usize, &T)>;
    }
    impl<T: Ord> SortVecBinarySearch<T> for Vec<T> {
        fn greater_equal(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x < y).1
        }
        fn greater_than(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x <= y).1
        }
        fn less_equal(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x <= y).0
        }
        fn less_than(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x < y).0
        }
    }
}
use sort_vec_binary_search::SortVecBinarySearch;

mod map_counter {
    use std::cmp::Ord;
    use std::collections::{BTreeMap, HashMap};
    use std::hash::Hash;
    pub trait MapCounter<T> {
        fn incr(&mut self, key: T);
        fn incr_by(&mut self, key: T, delta: usize);
        fn decr(&mut self, key: &T);
        fn decr_by(&mut self, key: &T, delta: usize);
    }
    impl<T: Ord + Clone> MapCounter<T> for BTreeMap<T, usize> {
        fn incr(&mut self, key: T) {
            self.incr_by(key, 1);
        }
        fn incr_by(&mut self, key: T, delta: usize) {
            *self.entry(key).or_insert(0) += delta;
        }
        fn decr(&mut self, key: &T) {
            self.decr_by(key, 1);
        }
        fn decr_by(&mut self, key: &T, delta: usize) {
            let v = self.entry(key.clone()).or_insert(0);
            debug_assert!(*v >= delta);
            *v -= delta;
            if *v == 0 {
                self.remove(key);
            }
        }
    }
    impl<T: Clone + Hash + Eq> MapCounter<T> for HashMap<T, usize> {
        fn incr(&mut self, key: T) {
            self.incr_by(key, 1);
        }
        fn incr_by(&mut self, key: T, delta: usize) {
            *self.entry(key).or_insert(0) += delta;
        }
        fn decr(&mut self, key: &T) {
            self.decr_by(key, 1);
        }
        fn decr_by(&mut self, key: &T, delta: usize) {
            let v = self.entry(key.clone()).or_insert(0);
            debug_assert!(*v >= delta);
            *v -= delta;
            if *v == 0 {
                self.remove(key);
            }
        }
    }
}
use map_counter::MapCounter;

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
struct Line2d(i64, i64, i64);
impl Line2d {
    // identify line from 2 differemt point
    fn new(y0: i64, x0: i64, y1: i64, x1: i64) -> Line2d {
        let mut b = y1 - y0;
        let mut a = x1 - x0;
        let mut c = x1 * y0 - x0 * y1;
        let r = gcd(a.abs(), gcd(b.abs(), c.abs()));
        a /= r;
        b /= r;
        c /= r;
        if (a == 0) && (b < 0) {
            a = -a;
            b = -b;
            c = -c;
        }
        if a < 0 {
            a = -a;
            b = -b;
            c = -c;
        }
        Line2d(a, b, c)
    }
}

mod strongly_connected_component {
    pub struct StronglyConnectedComponent {
        n: usize,
        pub graph: Vec<Vec<usize>>,
        bwd_graph: Vec<Vec<usize>>,
    }
    impl StronglyConnectedComponent {
        pub fn new(n: usize) -> StronglyConnectedComponent {
            StronglyConnectedComponent {
                n,
                graph: vec![vec![]; n],
                bwd_graph: vec![vec![]; n],
            }
        }
        pub fn add(&mut self, from: usize, into: usize) {
            self.graph[from].push(into);
            self.bwd_graph[into].push(from);
        }
        pub fn decompose(&mut self) -> Vec<Vec<usize>> {
            let mut scc = Vec::<Vec<usize>>::new();
            let mut fwd_seen = vec![false; self.n];
            let mut order = Vec::<usize>::new();
            for i in 0..self.n {
                if !fwd_seen[i] {
                    StronglyConnectedComponent::fwd_dfs(
                        &self.graph,
                        i,
                        None,
                        &mut fwd_seen,
                        &mut order,
                    );
                }
            }
            order.reverse();
            let mut bwd_seen = vec![false; self.n];
            for i_ in &order {
                let i = *i_;
                if !bwd_seen[i] {
                    let mut grp = Vec::<usize>::new();
                    StronglyConnectedComponent::bwd_dfs(
                        &self.bwd_graph,
                        i,
                        None,
                        &mut bwd_seen,
                        &mut grp,
                    );
                    grp.reverse();
                    scc.push(grp);
                }
            }
            scc
        }
        fn bwd_dfs(
            graph: &Vec<Vec<usize>>,
            v: usize,
            pre: Option<usize>,
            seen: &mut Vec<bool>,
            grp: &mut Vec<usize>,
        ) {
            seen[v] = true;
            for nv_ in &graph[v] {
                let nv = *nv_;
                if let Some(pre_v) = pre {
                    if nv == pre_v {
                        continue;
                    }
                }
                if !seen[nv] {
                    StronglyConnectedComponent::bwd_dfs(graph, nv, Some(v), seen, grp);
                }
            }
            grp.push(v);
        }
        fn fwd_dfs(
            graph: &Vec<Vec<usize>>,
            v: usize,
            pre: Option<usize>,
            seen: &mut Vec<bool>,
            order: &mut Vec<usize>,
        ) {
            seen[v] = true;
            for nv_ in &graph[v] {
                let nv = *nv_;
                if let Some(pre_v) = pre {
                    if nv == pre_v {
                        continue;
                    }
                }
                if !seen[nv] {
                    StronglyConnectedComponent::fwd_dfs(graph, nv, Some(v), seen, order);
                }
            }
            order.push(v);
        }
    }
}
use strongly_connected_component::StronglyConnectedComponent as Scc;

mod pair {
    use std::ops::{Add, AddAssign, Sub, SubAssign};
    #[derive(Debug, Clone, Copy)]
    pub struct Pair<X, Y> {
        pub x: X,
        pub y: Y,
    }
    impl<X: AddAssign, Y: AddAssign> AddAssign for Pair<X, Y> {
        fn add_assign(&mut self, rhs: Self) {
            self.x += rhs.x;
            self.y += rhs.y;
        }
    }
    impl<X: Add<Output = X>, Y: Add<Output = Y>> Add for Pair<X, Y> {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            Self {
                x: self.x + rhs.x,
                y: self.y + rhs.y,
            }
        }
    }
    impl<X: SubAssign, Y: SubAssign> SubAssign for Pair<X, Y> {
        fn sub_assign(&mut self, rhs: Self) {
            self.x -= rhs.x;
            self.y -= rhs.y;
        }
    }
    impl<X: Sub<Output = X>, Y: Sub<Output = Y>> Sub for Pair<X, Y> {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self::Output {
            Self {
                x: self.x - rhs.x,
                y: self.y - rhs.y,
            }
        }
    }
}
use pair::Pair;

mod usize_move_delta {
    pub trait MoveDelta<T> {
        fn move_delta(self, delta: T, lim_lo: usize, lim_hi: usize) -> Option<usize>;
    }
    impl<T: Copy + Into<i64>> MoveDelta<T> for usize {
        fn move_delta(self, delta: T, lim_lo: usize, lim_hi: usize) -> Option<usize> {
            let delta: i64 = delta.into();
            let added: i64 = self as i64 + delta;
            let lim_lo: i64 = lim_lo as i64;
            let lim_hi: i64 = lim_hi as i64;
            if (lim_lo <= added) && (added <= lim_hi) {
                Some(added as usize)
            } else {
                None
            }
        }
    }
}
use usize_move_delta::MoveDelta;

fn exit_by<T: std::fmt::Display>(msg: T) {
    println!("{}", msg);
    std::process::exit(0);
}

pub trait Permutation<T> {
    fn next_permutation(&self) -> Option<Vec<T>>;
    fn prev_permutation(&self) -> Option<Vec<T>>;
}
impl<T: Copy + Ord> Permutation<T> for Vec<T> {
    fn next_permutation(&self) -> Option<Vec<T>> {
        let n = self.len();
        if n == 0 {
            return None;
        }
        let mut seen = std::collections::BTreeMap::<T, usize>::new();
        seen.incr(*self.last().unwrap());
        for i in (0..n).rev().skip(1) {
            seen.incr(self[i]);
            if self[i] < self[i + 1] {
                let mut p = vec![];
                for &lv in self.iter().take(i) {
                    p.push(lv);
                }
                let &rv = seen.greater_than(&self[i]).unwrap().0;
                p.push(rv);
                seen.remove(&rv);
                while let Some((&rv, _nm)) = seen.iter().next() {
                    p.push(rv);
                    seen.decr(&rv);
                }
                return Some(p);
            }
        }
        None
    }
    fn prev_permutation(&self) -> Option<Vec<T>> {
        let n = self.len();
        if n == 0 {
            return None;
        }
        let mut seen = std::collections::BTreeMap::<T, usize>::new();
        seen.incr(*self.last().unwrap());
        for i in (0..n).rev().skip(1) {
            seen.incr(self[i]);
            if self[i] > self[i + 1] {
                let mut p = vec![];
                for &lv in self.iter().take(i) {
                    p.push(lv);
                }
                let &rv = seen.less_than(&self[i]).unwrap().0;
                p.push(rv);
                seen.remove(&rv);
                while let Some((&rv, _nm)) = seen.iter().next_back() {
                    p.push(rv);
                    seen.decr(&rv);
                }
                return Some(p);
            }
        }
        None
    }
}
pub struct PermutationIterator<T> {
    v: Vec<T>,
    is_finished: bool,
}
impl<T: Copy + Ord + Clone> PermutationIterator<T> {
    pub fn new(mut v: Vec<T>) -> PermutationIterator<T> {
        v.sort();
        PermutationIterator {
            v,
            is_finished: false,
        }
    }
}
impl<T: Copy + Ord + Clone> Iterator for PermutationIterator<T> {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_finished {
            // next perm doesn't exist.
            None
        } else if let Some(nxt) = self.v.next_permutation() {
            // return self state, and update self for future use.
            let ret = Some(self.v.clone());
            self.v = nxt;
            ret
        } else {
            // this time is the last.
            self.is_finished = true;
            Some(self.v.clone())
        }
    }
}

pub trait IntoPermutations<T: Copy + Ord + Clone> {
    fn into_permutations(self) -> PermutationIterator<T>;
}
// implement for ones that has IntoIterator.
impl<T: Copy + Ord + Clone, I: IntoIterator<Item = T>> IntoPermutations<T> for I {
    fn into_permutations(self) -> PermutationIterator<T> {
        PermutationIterator::new(self.into_iter().collect())
    }
}

mod add_header {
    pub trait AddHeader<T> {
        fn add_header(&mut self, add_val: T);
    }
    impl<T> AddHeader<T> for Vec<T>
    where
        Vec<T>: Clone,
    {
        fn add_header(&mut self, add_val: T) {
            let cpy = self.clone();
            self.clear();
            self.push(add_val);
            for cpy_val in cpy {
                self.push(cpy_val);
            }
        }
    }
}
use add_header::AddHeader;

mod auto_sort_vec {
    use crate::segment_tree::SegmentTree;
    pub struct AutoSortVec {
        max_val: usize,
        st: SegmentTree<usize>,
    }
    impl AutoSortVec {
        pub fn new(max_val: usize) -> AutoSortVec {
            AutoSortVec {
                max_val,
                st: SegmentTree::<usize>::new(max_val + 1, |x, y| x + y, 0),
            }
        }
        pub fn len(&self) -> usize {
            self.st.query(0, self.max_val)
        }
        pub fn push(&mut self, val: usize) {
            self.st.add(val, 1);
        }
        pub fn remove_value(&mut self, val: usize) {
            self.st.sub(val, 1);
        }
        pub fn value_to_index(&self, val: usize) -> usize {
            if val == 0 {
                0
            } else {
                self.st.query(0, val - 1)
            }
        }
        pub fn at(&self, idx: usize) -> usize {
            let idx1 = idx + 1;
            if self.st.get(0) >= idx1 {
                0
            } else if self.st.query(0, self.max_val - 1) < idx1 {
                self.max_val
            } else {
                let mut l = 0;
                let mut r = self.max_val;
                while r - l > 1 {
                    let m = (r + l) / 2;
                    let sm = self.st.query(0, m);
                    if sm < idx1 {
                        l = m;
                    } else {
                        r = m;
                    }
                }
                r
            }
        }
    }
}
use auto_sort_vec::AutoSortVec;

mod my_string {
    use std::ops::{Index, IndexMut};
    use std::slice::SliceIndex;
    #[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
    pub struct Str {
        vc: Vec<char>,
    }
    impl Str {
        pub fn new() -> Self {
            Self { vc: vec![] }
        }
        pub fn from(s: &str) -> Self {
            Self {
                vc: s.to_string().chars().collect::<Vec<char>>(),
            }
        }
        pub fn len(&self) -> usize {
            self.vc.len()
        }
        pub fn clear(&mut self) {
            self.vc.clear()
        }
        pub fn is_empty(&self) -> bool {
            self.vc.is_empty()
        }
        pub fn first(&self) -> Option<&char> {
            self.vc.first()
        }
        pub fn last(&self) -> Option<&char> {
            self.vc.last()
        }
        pub fn push(&mut self, c: char) {
            self.vc.push(c);
        }
        pub fn push_str(&mut self, s: &str) {
            for c in s.to_string().chars().collect::<Vec<char>>().into_iter() {
                self.push(c);
            }
        }
        pub fn pop(&mut self) -> Option<char> {
            self.vc.pop()
        }
        pub fn into_iter(self) -> std::vec::IntoIter<char> {
            self.vc.into_iter()
        }
        pub fn iter(&self) -> std::slice::Iter<char> {
            self.vc.iter()
        }
        pub fn iter_mut(&mut self) -> std::slice::IterMut<char> {
            self.vc.iter_mut()
        }
        pub fn swap(&mut self, a: usize, b: usize) {
            self.vc.swap(a, b);
        }
        pub fn reverse(&mut self) {
            self.vc.reverse();
        }
        pub fn find(&self, p: &Str) -> Option<usize> {
            let s: String = self.vc.iter().collect::<String>();
            let p: String = p.vc.iter().collect::<String>();
            s.find(&p)
        }
        pub fn rfind(&self, p: &Str) -> Option<usize> {
            let s: String = self.vc.iter().collect::<String>();
            let p: String = p.vc.iter().collect::<String>();
            s.rfind(&p)
        }
        pub fn into_values(self, base: char) -> Vec<usize> {
            self.vc
                .into_iter()
                .map(|c| (c as u8 - base as u8) as usize)
                .collect::<Vec<usize>>()
        }
        pub fn sort(&mut self) {
            self.vc.sort();
        }
        pub fn remove(&mut self, index: usize) -> char {
            self.vc.remove(index)
        }
    }
    impl std::str::FromStr for Str {
        type Err = ();
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Ok(Str {
                vc: s.to_string().chars().collect::<Vec<char>>(),
            })
        }
    }
    impl<Idx: SliceIndex<[char]>> Index<Idx> for Str {
        type Output = Idx::Output;
        fn index(&self, i: Idx) -> &Self::Output {
            &self.vc[i]
        }
    }
    impl<Idx: SliceIndex<[char]>> IndexMut<Idx> for Str {
        fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
            &mut self.vc[index]
        }
    }
    impl std::ops::Add<Str> for Str {
        type Output = Str;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            for c in rhs.into_iter() {
                ret.vc.push(c);
            }
            ret
        }
    }
    impl std::ops::AddAssign<Str> for Str {
        fn add_assign(&mut self, rhs: Self) {
            for c in rhs.into_iter() {
                self.vc.push(c);
            }
        }
    }
    impl std::ops::Add<char> for Str {
        type Output = Str;
        fn add(self, rhs: char) -> Self::Output {
            let mut ret = self;
            ret.vc.push(rhs);
            ret
        }
    }
    impl std::ops::AddAssign<char> for Str {
        fn add_assign(&mut self, rhs: char) {
            self.vc.push(rhs);
        }
    }
    impl std::fmt::Display for Str {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", self.vc.iter().collect::<String>())
        }
    }
    impl std::fmt::Debug for Str {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", self.vc.iter().collect::<String>())
        }
    }
}
use my_string::Str;

mod rolling_hash {
    use u64 as htype;
    const MOD: htype = 10000000000000061;
    pub struct RollingHash {
        cum_hashes: Vec<htype>,
        base: usize,
        base_powers: Vec<htype>,
        base_powers_inv: Vec<htype>,
    }
    pub struct RollingHashValue<'a> {
        org: &'a RollingHash,
        i0: usize,
        i1: usize,
    }
    pub trait GenRollingHash {
        fn rolling_hash(&self, base: usize) -> RollingHash;
    }
    impl GenRollingHash for Vec<usize> {
        fn rolling_hash(&self, base: usize) -> RollingHash {
            RollingHash::new(self, base)
        }
    }
    impl RollingHash {
        fn new(values: &Vec<usize>, base: usize) -> RollingHash {
            let n = values.len();

            let mut base_powers = vec![1; n];
            for p in 1..n {
                base_powers[p] = (base_powers[p - 1] * base as htype) % MOD;
            }

            let inv_base = {
                let mut p = MOD - 2;
                let mut ret: htype = 1;
                let mut mul = base as htype;
                while p > 0 {
                    if p & 1 != 0 {
                        ret = (ret * mul) % MOD;
                    }
                    p >>= 1;
                    mul = (mul * mul) % MOD;
                }
                ret
            };

            let mut base_powers_inv = vec![1; n];
            for p in 1..n {
                base_powers_inv[p] = (base_powers_inv[p - 1] * inv_base) % MOD;
            }

            let mut cum_hashes = (0..n)
                .map(|i| (values[i] as htype * base_powers[i]) % MOD)
                .collect::<Vec<_>>();
            for i in 1..n {
                cum_hashes[i] += cum_hashes[i - 1];
                cum_hashes[i] %= MOD;
            }

            Self {
                cum_hashes,
                base,
                base_powers,
                base_powers_inv,
            }
        }
        pub fn hash(&self, i0: usize, i1: usize) -> RollingHashValue {
            RollingHashValue { org: self, i0, i1 }
        }
    }
    impl<'a> RollingHashValue<'a> {
        fn get(&'a self) -> htype {
            if self.i0 > 0 {
                ((MOD + self.org.cum_hashes[self.i1] - self.org.cum_hashes[self.i0 - 1])
                    * self.org.base_powers_inv[self.i0])
                    % MOD
            } else {
                self.org.cum_hashes[self.i1]
            }
        }
    }
    impl PartialEq for RollingHashValue<'_> {
        fn eq(&self, other: &Self) -> bool {
            debug_assert!(self.i1 - self.i0 == other.i1 - other.i0);
            self.get() == other.get()
        }
    }
}
use rolling_hash::*;

mod rational {
    use crate::gcd::gcd;
    use std::cmp::Ordering;
    use std::fmt;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Rational {
        pub num: i64,
        pub denom: i64,
    }
    impl Rational {
        pub fn new(num: i64, denom: i64) -> Self {
            if num == 0 {
                if denom == 0 {
                    panic!("0/0 is indefinite.")
                } else {
                    Self { num: 0, denom: 1 }
                }
            } else if denom == 0 {
                Self { num: 1, denom: 0 }
            } else {
                let (num, denom) = {
                    if denom < 0 {
                        (-num, -denom)
                    } else {
                        (num, denom)
                    }
                };
                let g = gcd(num.abs(), denom.abs());
                debug_assert!(denom >= 0);
                Self {
                    num: num / g,
                    denom: denom / g,
                }
            }
        }
    }
    impl AddAssign<Self> for Rational {
        fn add_assign(&mut self, rhs: Self) {
            let d0 = self.denom.abs();
            let d1 = rhs.denom.abs();
            let denom = d0 * (d1 / gcd(d0, d1));
            let n0 = self.num * (denom / d0);
            let n1 = rhs.num * (denom / d1);
            *self = Self::new(n0 + n1, denom);
        }
    }
    impl Add<Self> for Rational {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret += rhs;
            ret
        }
    }
    impl SubAssign<Self> for Rational {
        fn sub_assign(&mut self, rhs: Self) {
            *self += Self::new(-rhs.num, rhs.denom);
        }
    }
    impl Sub<Self> for Rational {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret -= rhs;
            ret
        }
    }
    impl MulAssign<Self> for Rational {
        fn mul_assign(&mut self, rhs: Self) {
            *self = Self::new(self.num * rhs.num, self.denom * rhs.denom);
        }
    }
    impl Mul<Self> for Rational {
        type Output = Self;
        fn mul(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret *= rhs;
            ret
        }
    }
    impl DivAssign<Self> for Rational {
        fn div_assign(&mut self, rhs: Self) {
            *self = Self::new(self.num * rhs.denom, rhs.num * self.denom);
        }
    }
    impl Div<Self> for Rational {
        type Output = Self;
        fn div(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret /= rhs;
            ret
        }
    }
    impl Neg for Rational {
        type Output = Self;
        fn neg(self) -> Self::Output {
            Self::new(-self.num, self.denom)
        }
    }
    impl PartialOrd for Rational {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            i64::partial_cmp(&(self.num * other.denom), &(self.denom * other.num))
        }
    }
    impl Ord for Rational {
        fn cmp(&self, other: &Self) -> Ordering {
            Self::partial_cmp(self, other).unwrap()
        }
    }
    impl fmt::Display for Rational {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.num as f64 / self.denom as f64)
        }
    }
    impl fmt::Debug for Rational {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.num as f64 / self.denom as f64)
        }
    }
}
use rational::Rational;

fn z_algo(s: &Str) -> Vec<usize> {
    // https://www.youtube.com/watch?v=f6ct5PQHqM0
    let n = s.len();
    let mut last_match = None;
    let mut ret = vec![0; n];
    ret[0] = n;
    for i in 1..n {
        let mut match_delta = 0;
        if let Some((m0, m1)) = last_match {
            if i < m1 {
                // reuse calculated info.
                if i + ret[i - m0] != m1 {
                    // built from old one, and finish.
                    ret[i] = min(ret[i - m0], m1 - i);
                    continue;
                } else {
                    // skip known range, and continues.
                    match_delta = m1 - i;
                }
            }
        }
        // expand until unmatch is found.
        while i + match_delta < n {
            if s[match_delta] == s[i + match_delta] {
                match_delta += 1;
            } else {
                break;
            }
        }
        // set header-match lentgh.
        ret[i] = match_delta;
        // update last match range for future use.
        if let Some((_m0, m1)) = last_match {
            if i + match_delta <= m1 {
                continue;
            }
        }
        last_match = Some((i, i + match_delta));
    }
    ret
}

fn convex_hull<
    T: Copy
        + PartialOrd<T>
        + Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>,
>(
    points: &[(T, T)],
) -> Vec<(T, T)> {
    fn outer_product<T: Copy + Add<Output = T> + Sub<Output = T> + Mul<Output = T>>(
        origin: (T, T),
        end0: (T, T),
        end1: (T, T),
    ) -> T {
        (end0.0 - origin.0) * (end1.1 - origin.1) - (end0.1 - origin.1) * (end1.0 - origin.0)
    }

    #[allow(clippy::eq_op)]
    let zero = points[0].0 - points[0].0;
    let mut points = points.to_vec();
    points.sort_by(|x, y| x.partial_cmp(y).unwrap());
    let mut ret = vec![];
    for &p in points.iter() {
        while ret.len() >= 2 {
            if outer_product(ret[ret.len() - 1], ret[ret.len() - 2], p) < zero {
                break;
            }
            ret.pop();
        }
        ret.push(p);
    }
    let t = ret.len();
    for p in points.into_iter().rev().skip(1) {
        while ret.len() > t {
            if outer_product(ret[ret.len() - 1], ret[ret.len() - 2], p) < zero {
                break;
            }
            ret.pop();
        }
        ret.push(p);
    }
    ret
}

mod matrix {
    use crate::Identity;
    use std::iter::Sum;
    use std::ops::{Add, Index, IndexMut, Mul, MulAssign, Sub};
    use std::slice::SliceIndex;
    #[derive(Clone)]
    pub struct Matrix<T> {
        h: usize,
        w: usize,
        vals: Vec<Vec<T>>,
    }
    impl<T: Clone + Copy + Identity + Sub<Output = T> + Mul + Sum<<T as Mul>::Output>> Matrix<T> {
        pub fn new(h: usize, w: usize) -> Self {
            let v1 = T::identity();
            #[allow(clippy::eq_op)]
            let v0 = v1 - v1;
            Self {
                h,
                w,
                vals: vec![vec![v0; w]; h],
            }
        }
        pub fn identity(h: usize, w: usize) -> Self {
            debug_assert!(h == w);
            let v1 = T::identity();
            #[allow(clippy::eq_op)]
            let v0 = v1 - v1;
            let mut vals = vec![vec![v0; w]; h];
            for (y, line) in vals.iter_mut().enumerate() {
                for (x, val) in line.iter_mut().enumerate() {
                    *val = if y == x { v1 } else { v0 };
                }
            }
            Self { h, w, vals }
        }
        pub fn pow(&self, mut p: usize) -> Self {
            let mut ret = Self::identity(self.h, self.w);
            let mut mul = self.clone();
            while p > 0 {
                if p & 1 != 0 {
                    ret = ret.clone() * mul.clone();
                }
                p >>= 1;
                mul = mul.clone() * mul.clone();
            }
            ret
        }
    }
    impl<T, Idx: SliceIndex<[Vec<T>]>> Index<Idx> for Matrix<T> {
        type Output = Idx::Output;
        fn index(&self, i: Idx) -> &Self::Output {
            &self.vals[i]
        }
    }
    impl<T, Idx: SliceIndex<[Vec<T>]>> IndexMut<Idx> for Matrix<T> {
        fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
            &mut self.vals[index]
        }
    }
    impl<T: Clone + Copy + Identity + Sub<Output = T> + Mul + Sum<<T as Mul>::Output>>
        Mul<Matrix<T>> for Matrix<T>
    {
        type Output = Matrix<T>;
        fn mul(self, rhs: Matrix<T>) -> Self::Output {
            debug_assert!(self.w == rhs.h);
            let mut ret = Self::new(self.h, rhs.w);
            for y in 0..ret.h {
                for x in 0..ret.w {
                    ret[y][x] = (0..self.w).map(|i| self[y][i] * rhs[i][x]).sum::<T>();
                }
            }
            ret
        }
    }
    impl<T: Clone + Copy + Identity + Sub<Output = T> + Mul + Sum<<T as Mul>::Output>> Mul<Vec<T>>
        for Matrix<T>
    {
        type Output = Vec<T>;
        fn mul(self, rhs: Vec<T>) -> Self::Output {
            debug_assert!(self.w == rhs.len());
            let v1 = T::identity();
            #[allow(clippy::eq_op)]
            let v0 = v1 - v1;
            let mut ret = vec![v0; self.h];
            for y in 0..self.h {
                ret[y] = (0..self.w).map(|x| self[y][x] * rhs[x]).sum::<T>();
            }
            ret
        }
    }
    impl<
            T: Clone
                + Copy
                + Identity
                + Add<Output = T>
                + Sub<Output = T>
                + Mul
                + Sum<<T as Mul>::Output>,
        > Add<Matrix<T>> for Matrix<T>
    {
        type Output = Matrix<T>;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = Matrix::<T>::new(self.h, self.w);
            for y in 0..self.h {
                for x in 0..self.w {
                    ret[y][x] = self[y][x] + rhs[y][x];
                }
            }
            ret
        }
    }
    impl<T: Clone + Copy + Identity + Sub<Output = T> + Mul + Sum<<T as Mul>::Output>>
        MulAssign<Matrix<T>> for Matrix<T>
    {
        fn mul_assign(&mut self, rhs: Matrix<T>) {
            *self = self.clone() * rhs;
        }
    }
}
use matrix::Matrix;

mod suffix_array {
    use crate::my_string;
    use crate::CoordinateCompress;
    use std::cmp::{min, Ord, Ordering};
    fn compare_sa(rank: &[i64], i: usize, j: usize, k: usize, n: usize) -> Ordering {
        if rank[i] != rank[j] {
            rank[i].cmp(&rank[j])
        } else {
            let ri = if i + k <= n { rank[i + k] } else { 0 };
            let rj = if j + k <= n { rank[j + k] } else { 0 };
            ri.cmp(&rj)
        }
    }
    fn construct_sa(s: &[usize]) -> Vec<usize> {
        let n = s.len();
        let mut sa = vec![0usize; n + 1];
        let mut rank = vec![0i64; n + 1];
        for i in 0..=n {
            sa[i] = i;
            rank[i] = if i < n { s[i] as i64 } else { -1 };
        }
        let mut nrank = rank.clone();
        let mut k = 1;
        while k <= n {
            sa.sort_by(|&i, &j| compare_sa(&rank, i, j, k, n));
            nrank[sa[0]] = 0;
            for i in 1..=n {
                nrank[sa[i]] = nrank[sa[i - 1]]
                    + if compare_sa(&rank, sa[i - 1], sa[i], k, n) == Ordering::Less {
                        1
                    } else {
                        0
                    };
            }
            std::mem::swap(&mut rank, &mut nrank);
            //
            k <<= 1;
        }
        sa.into_iter().skip(1).collect::<Vec<_>>()
    }
    pub trait ToSuffixArray {
        fn to_suffix_array(&self) -> Vec<usize>;
    }
    impl ToSuffixArray for Vec<usize> {
        fn to_suffix_array(&self) -> Vec<usize> {
            construct_sa(self)
        }
    }
}
use suffix_array::ToSuffixArray;

mod flow {
    use crate::change_min_max::ChangeMinMax;
    use std::cmp::Reverse;
    use std::collections::BinaryHeap;
    #[derive(Clone, Copy)]
    pub struct Edge {
        pub to: usize,
        pub rev_idx: usize, // index of paired edge at node "to".
        pub capacity: i64,  // - inf <= flow <= capacity
        pub flow: i64,      // flow can be negative.
        pub cost: i64,      // for min-cost flow
    }
    pub struct Flow {
        pub g: Vec<Vec<Edge>>,
    }
    impl Flow {
        pub fn new(n: usize) -> Self {
            Self { g: vec![vec![]; n] }
        }
        pub fn add_edge(&mut self, from: usize, to: usize, capacity: i64) {
            let rev_idx = self.g[to].len();
            self.g[from].push(Edge {
                to,
                rev_idx,
                capacity,
                flow: 0,
                cost: 0,
            });
            let rev_idx = self.g[from].len() - 1;
            self.g[to].push(Edge {
                to: from,
                rev_idx,
                capacity: 0,
                flow: 0,
                cost: 0,
            });
        }
        pub fn add_cost_edge(&mut self, from: usize, to: usize, capacity: i64, cost: i64) {
            let rev_idx = self.g[to].len();
            self.g[from].push(Edge {
                to,
                rev_idx,
                capacity,
                flow: 0,
                cost,
            });
            let rev_idx = self.g[from].len() - 1;
            self.g[to].push(Edge {
                to: from,
                rev_idx,
                capacity: 0,
                flow: 0,
                cost: -cost,
            });
        }
        fn bfs(g: &[Vec<Edge>], source: usize) -> Vec<Option<usize>> {
            let mut level = vec![None; g.len()];
            level[source] = Some(0);
            let mut que = std::collections::VecDeque::new();
            que.push_back(source);
            while let Some(v) = que.pop_front() {
                let nxt_level = level[v].unwrap() + 1;
                for edge in g[v].iter().copied() {
                    if level[edge.to].is_none() && (edge.capacity > edge.flow) {
                        level[edge.to] = Some(nxt_level);
                        que.push_back(edge.to);
                    }
                }
            }
            level
        }
        fn dfs(
            g: &mut [Vec<Edge>],
            v: usize,
            sink: usize,
            flow: i64,
            search_cnt: &mut [usize],
            level: &[Option<usize>],
        ) -> i64 {
            if v == sink {
                return flow;
            }
            while search_cnt[v] < g[v].len() {
                let (to, rev_idx, remain_capacity) = {
                    let edge = g[v][search_cnt[v]];
                    (edge.to, edge.rev_idx, edge.capacity - edge.flow)
                };
                if let Some(nxt_level) = level[to] {
                    if (level[v].unwrap() < nxt_level) && (remain_capacity > 0) {
                        let additional_flow = Self::dfs(
                            g,
                            to,
                            sink,
                            std::cmp::min(flow, remain_capacity),
                            search_cnt,
                            level,
                        );
                        if additional_flow > 0 {
                            g[v][search_cnt[v]].flow += additional_flow;
                            g[to][rev_idx].flow -= additional_flow;
                            return additional_flow;
                        }
                    }
                }
                search_cnt[v] += 1;
            }
            0
        }
        pub fn max_flow(&mut self, source: usize, sink: usize) -> i64 {
            let inf = 1i64 << 60;
            let mut flow = 0;
            loop {
                let level = Self::bfs(&self.g, source);
                if level[sink].is_none() {
                    break;
                }
                let mut search_cnt = vec![0; self.g.len()];
                loop {
                    let additional_flow =
                        Self::dfs(&mut self.g, source, sink, inf, &mut search_cnt, &level);
                    if additional_flow > 0 {
                        flow += additional_flow;
                    } else {
                        break;
                    }
                }
            }
            flow
        }
        pub fn min_cost_flow(&mut self, source: usize, sink: usize, mut flow: i64) -> Option<i64> {
            let mut min_cost = 0;
            let mut h = vec![0; self.g.len()];
            let mut dist = vec![None; self.g.len()];
            let mut prev = vec![None; self.g.len()];
            while flow > 0 {
                let mut que = BinaryHeap::new();
                que.push((Reverse(0), source));
                dist.iter_mut().for_each(|dist| *dist = None);
                dist[source] = Some(0);
                while let Some((Reverse(d), v)) = que.pop() {
                    if dist[v].unwrap() != d {
                        continue;
                    }
                    for (ei, e) in self.g[v].iter().enumerate() {
                        if e.flow >= e.capacity {
                            continue;
                        }
                        let nd = d + e.cost + h[v] - h[e.to];
                        if dist[e.to].chmin(nd) {
                            prev[e.to] = Some((v, ei));
                            que.push((Reverse(nd), e.to));
                        }
                    }
                }
                dist[sink]?;
                h.iter_mut().zip(dist.iter()).for_each(|(h, d)| {
                    if let Some(d) = d {
                        *h += d;
                    }
                });
                let mut delta_flow = flow;
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        let e = &self.g[pv][pei];
                        delta_flow.chmin(e.capacity - e.flow);
                        v = pv;
                    }
                }
                flow -= delta_flow;
                min_cost += delta_flow * h[sink];
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        self.g[pv][pei].flow += delta_flow;
                        let rev_idx = self.g[pv][pei].rev_idx;
                        self.g[v][rev_idx].flow -= delta_flow;
                        v = pv;
                    }
                }
            }
            Some(min_cost)
        }
    }
}
use flow::Flow;

mod convolution {
    // https://github.com/atcoder/ac-library/blob/master/atcoder/convolution.hpp
    use crate::{modint::ModInt as mint, IntegerOperation};
    pub fn convolution(arga: &[mint], argb: &[mint]) -> Vec<mint> {
        let n = arga.len();
        let m = argb.len();
        let z = 1 << ceil_pow2(n + m - 1);
        let mut a = vec![mint::from(0); z];
        let mut b = vec![mint::from(0); z];
        for (a, &arga) in a.iter_mut().zip(arga.iter()) {
            *a = arga;
        }
        butterfly(&mut a);
        for (b, &argb) in b.iter_mut().zip(argb.iter()) {
            *b = argb;
        }
        butterfly(&mut b);
        for (a, b) in a.iter_mut().zip(b.into_iter()) {
            *a *= b;
        }
        butterfly_inv(&mut a);
        while a.len() > n + m - 1 {
            a.pop();
        }
        let iz = mint::from(1) / mint::from(z);
        for a in a.iter_mut() {
            *a *= iz;
        }
        a
    }
    // returns 'r' s.t. 'r^(m - 1) == 1 (mod m)'
    fn primitive_root(m: i64) -> i64 {
        debug_assert!(is_prime(m));
        if m == 2 {
            return 1;
        }
        if m == 167772161 {
            return 3;
        }
        if m == 469762049 {
            return 3;
        }
        if m == 754974721 {
            return 11;
        }
        if m == 998244353 {
            return 3;
        }
        if m == 1000000007 {
            return 5;
        }
        let divs = ((m - 1) / 2).into_primes();

        for g in 2.. {
            let mut ok = true;
            for (&div, _) in divs.iter() {
                fn pow_mod(x: i64, mut p: i64, m: i64) -> i64 {
                    let mut ret = 1;
                    let mut mul = x % m;
                    while p > 0 {
                        if p & 1 != 0 {
                            ret *= mul;
                            ret %= m;
                        }
                        p >>= 1;
                        mul *= mul;
                        mul %= m;
                    }
                    ret
                }

                if pow_mod(g, (m - 1) / div, m) == 1 {
                    ok = false;
                    break;
                }
            }
            if ok {
                return g;
            }
        }
        unreachable!();
    }
    fn is_prime(x: i64) -> bool {
        if x == 1 {
            return false;
        }
        for i in 2.. {
            if i * i > x {
                return true;
            }
            if x % i == 0 {
                return false;
            }
        }
        unreachable!();
    }
    struct FFTinfo {
        root: Vec<mint>,  // root[i]^(2^i) == 1
        iroot: Vec<mint>, // root[i] * iroot[i] == 1
        rate2: Vec<mint>,
        irate2: Vec<mint>,
        rate3: Vec<mint>,
        irate3: Vec<mint>,
    }
    // returns minimum non-negative `x` s.t. `(n & (1 << x)) != 0`
    fn bsf(n: usize) -> usize {
        let mut x = 0;
        while (n & (1 << x)) == 0 {
            x += 1;
        }
        x
    }
    impl FFTinfo {
        fn new() -> Self {
            let rank2 = bsf((mint::get_mod() - 1) as usize);
            let mut root = vec![mint::from(0); rank2 + 1];
            let mut iroot = vec![mint::from(0); rank2 + 1];
            let mut rate2 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 2 + 1) as usize];
            let mut irate2 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 2 + 1) as usize];
            let mut rate3 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 3 + 1) as usize];
            let mut irate3 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 3 + 1) as usize];

            let g = primitive_root(mint::get_mod());
            root[rank2] = mint::from(g).pow((mint::get_mod() as usize - 1) >> rank2);
            iroot[rank2] = mint::from(1) / root[rank2];
            for i in (0..rank2).rev() {
                root[i] = root[i + 1] * root[i + 1];
                iroot[i] = iroot[i + 1] * iroot[i + 1];
            }

            {
                let mut prod = mint::from(1);
                let mut iprod = mint::from(1);
                for i in 0..=(rank2 - 2) {
                    rate2[i] = root[i + 2] * prod;
                    irate2[i] = iroot[i + 2] * iprod;
                    prod *= iroot[i + 2];
                    iprod *= root[i + 2];
                }
            }
            {
                let mut prod = mint::from(1);
                let mut iprod = mint::from(1);
                for i in 0..=(rank2 - 3) {
                    rate3[i] = root[i + 3] * prod;
                    irate3[i] = iroot[i + 3] * iprod;
                    prod *= iroot[i + 3];
                    iprod *= root[i + 3];
                }
            }

            Self {
                root,
                iroot,
                rate2,
                irate2,
                rate3,
                irate3,
            }
        }
    }
    fn ceil_pow2(n: usize) -> usize {
        let mut x = 0;
        while (1 << x) < n {
            x += 1;
        }
        x
    }
    fn butterfly(a: &mut [mint]) {
        let n = a.len();
        let h = ceil_pow2(n);

        let info = FFTinfo::new();

        let mut len = 0; // a[i, i+(n>>len), i+2*(n>>len), ..] is transformed
        while len < h {
            if h - len == 1 {
                let p = 1 << (h - len - 1);
                let mut rot = mint::from(1);
                for s in 0..(1 << len) {
                    let offset = s << (h - len);
                    for i in 0..p {
                        let l = a[i + offset];
                        let r = a[i + offset + p] * rot;
                        a[i + offset] = l + r;
                        a[i + offset + p] = l - r;
                    }
                    if s + 1 != (1 << len) {
                        rot *= info.rate2[bsf(!s)];
                    }
                }
                len += 1;
            } else {
                // 4-base
                let p = 1 << (h - len - 2);
                let mut rot = mint::from(1);
                let imag = info.root[2];
                for s in 0..(1 << len) {
                    let rot2 = rot * rot;
                    let rot3 = rot2 * rot;
                    let offset = s << (h - len);
                    for i in 0..p {
                        let mod2 = mint::get_mod() * mint::get_mod();
                        let a0 = a[i + offset].val();
                        let a1 = a[i + offset + p].val() * rot.val();
                        let a2 = a[i + offset + 2 * p].val() * rot2.val();
                        let a3 = a[i + offset + 3 * p].val() * rot3.val();
                        let a1na3imag = mint::from(a1 + mod2 - a3).val() * imag.val();
                        let na2 = mod2 - a2;
                        a[i + offset] = mint::from(a0 + a2 + a1 + a3);
                        a[i + offset + p] = mint::from(a0 + a2 + (2 * mod2 - (a1 + a3)));
                        a[i + offset + 2 * p] = mint::from(a0 + na2 + a1na3imag);
                        a[i + offset + 3 * p] = mint::from(a0 + na2 + (mod2 - a1na3imag));
                    }
                    if s + 1 != (1 << len) {
                        rot *= info.rate3[bsf(!s)];
                    }
                }
                len += 2;
            }
        }
    }
    fn butterfly_inv(a: &mut [mint]) {
        let n = a.len();
        let h = ceil_pow2(n);

        let info = FFTinfo::new();

        let mut len = h; // a[i, i+(n>>len), i+2*(n>>len), ..] is transformed
        while len > 0 {
            if len == 1 {
                let p = 1 << (h - len);
                let mut irot = mint::from(1);
                for s in 0..(1 << (len - 1)) {
                    let offset = s << (h - len + 1);
                    for i in 0..p {
                        let l = a[i + offset];
                        let r = a[i + offset + p];
                        a[i + offset] = l + r;
                        a[i + offset + p] =
                            mint::from((mint::get_mod() + l.val() - r.val()) * irot.val());
                    }
                    if s + 1 != (1 << (len - 1)) {
                        irot *= info.irate2[bsf(!s)];
                    }
                }
                len -= 1;
            } else {
                // 4-base
                let p = 1 << (h - len);
                let mut irot = mint::from(1);
                let iimag = info.iroot[2];
                for s in 0..(1 << (len - 2)) {
                    let irot2 = irot * irot;
                    let irot3 = irot2 * irot;
                    let offset = s << (h - len + 2);
                    for i in 0..p {
                        let a0 = a[i + offset].val();
                        let a1 = a[i + offset + p].val();
                        let a2 = a[i + offset + 2 * p].val();
                        let a3 = a[i + offset + 3 * p].val();
                        let a2na3iimag =
                            mint::from((mint::get_mod() + a2 - a3) * iimag.val()).val();
                        a[i + offset] = mint::from(a0 + a1 + a2 + a3);
                        a[i + offset + p] =
                            mint::from((a0 + (mint::get_mod() - a1) + a2na3iimag) * irot.val());
                        a[i + offset + 2 * p] = mint::from(
                            (a0 + a1 + (mint::get_mod() - a2) + (mint::get_mod() - a3))
                                * irot2.val(),
                        );
                        a[i + offset + 3 * p] = mint::from(
                            (a0 + (mint::get_mod() - a1) + (mint::get_mod() - a2na3iimag))
                                * irot3.val(),
                        );
                    }
                    if s + 1 != (1 << (len - 2)) {
                        irot *= info.irate3[bsf(!s)];
                    }
                }
                len -= 2;
            }
        }
    }
}
use convolution::convolution;

mod manhattan_mst {
    use crate::change_min_max::ChangeMinMax;
    use crate::{segment_tree::SegmentTree, CoordinateCompress, UnionFind};
    use std::cmp::{min, Reverse};
    use std::collections::BinaryHeap;
    pub struct ManhattanMST {
        points: Vec<(usize, (i64, i64))>,
    }
    impl ManhattanMST {
        pub fn new() -> Self {
            Self { points: vec![] }
        }
        pub fn push(&mut self, pt: (i64, i64)) {
            self.points.push((self.points.len(), pt));
        }
        fn mst(mut edges: Vec<(i64, usize, usize)>, n: usize) -> Vec<Vec<(i64, usize)>> {
            let mut uf = UnionFind::new(n);
            let mut g = vec![vec![]; n];
            edges.sort();
            for (delta, i, j) in edges {
                if !uf.same(i, j) {
                    uf.unite(i, j);
                    g[i].push((delta, j));
                    g[j].push((delta, i));
                }
            }
            g
        }
        pub fn minimum_spanning_tree(&mut self) -> Vec<Vec<(i64, usize)>> {
            let n = self.points.len();
            let mut edges = vec![];
            let inf = 1i64 << 60;
            for h0 in 0..2 {
                for h1 in 0..2 {
                    let y_enc = self
                        .points
                        .iter()
                        .map(|&(_i, (y, _x))| y)
                        .collect::<Vec<_>>()
                        .compress_encoder();
                    for h2 in 0..2 {
                        let mut st = SegmentTree::<(usize, i64)>::new(
                            n,
                            |(i0, ypx0), (i1, ypx1)| {
                                if ypx0 < ypx1 {
                                    (i0, ypx0)
                                } else {
                                    (i1, ypx1)
                                }
                            },
                            (0, inf),
                        );
                        self.points
                            .sort_by(|(_i0, (y0, x0)), (_i1, (y1, x1))| (y0 - x0).cmp(&(y1 - x1)));
                        for &(i, (y, x)) in self.points.iter() {
                            let ey = y_enc[&y];
                            let q = st.query(ey, n - 1);
                            if q.1 != inf {
                                let delta = q.1 - (y + x);
                                debug_assert!(delta >= 0);
                                edges.push((delta, i, q.0));
                            }
                            //
                            if st.get(ey).1 > y + x {
                                st.set(ey, (i, y + x));
                            }
                        }
                        if h2 == 0 {
                            self.points.iter_mut().for_each(|(_i, (_y, x))| *x = -(*x));
                        }
                    }
                    if h1 == 0 {
                        self.points.iter_mut().for_each(|(_i, (y, _x))| *y = -(*y));
                    }
                }
                if h0 == 0 {
                    self.points
                        .iter_mut()
                        .for_each(|(_i, (y, x))| std::mem::swap(x, y));
                }
            }
            Self::mst(edges, n)
        }
    }
}
use manhattan_mst::ManhattanMST;

mod mo {
    use std::vec::IntoIter;
    pub struct Mo {
        ls: Vec<usize>,
        rs: Vec<usize>,
    }
    pub struct MoIterator {
        index_iter: IntoIter<usize>,
        ls: Vec<usize>,
        rs: Vec<usize>,
    }
    impl Mo {
        pub fn new() -> Self {
            Self {
                ls: vec![],
                rs: vec![],
            }
        }
        pub fn add_range_queue(&mut self, l: usize, r: usize) {
            self.ls.push(l);
            self.rs.push(r);
        }
        pub fn into_iter(self) -> MoIterator {
            let n = self.rs.iter().max().unwrap() + 1;
            let q = self.rs.len();
            let d = n / ((q as f64).sqrt() as usize + 1) + 1;
            let mut indexes = (0..q).collect::<Vec<_>>();
            indexes.sort_by_cached_key(|&i| {
                let div = self.ls[i] / d;
                if div % 2 == 0 {
                    (div, self.rs[i])
                } else {
                    (div, n - self.rs[i])
                }
            });
            MoIterator {
                index_iter: indexes.into_iter(),
                ls: self.ls,
                rs: self.rs,
            }
        }
    }
    impl Iterator for MoIterator {
        type Item = (usize, (usize, usize));
        fn next(&mut self) -> Option<Self::Item> {
            if let Some(i) = self.index_iter.next() {
                Some((i, (self.ls[i], self.rs[i])))
            } else {
                None
            }
        }
    }
}
use mo::*;

mod procon_reader {
    use std::fmt::Debug;
    use std::io::Read;
    use std::str::FromStr;
    pub fn read<T: FromStr>() -> T
    where
        <T as FromStr>::Err: Debug,
    {
        let stdin = std::io::stdin();
        let mut stdin_lock = stdin.lock();
        let mut u8b: [u8; 1] = [0];
        loop {
            let mut buf: Vec<u8> = Vec::with_capacity(16);
            loop {
                let res = stdin_lock.read(&mut u8b);
                if res.unwrap_or(0) == 0 || u8b[0] <= b' ' {
                    break;
                } else {
                    buf.push(u8b[0]);
                }
            }
            if !buf.is_empty() {
                let ret = String::from_utf8(buf).unwrap();
                return ret.parse().unwrap();
            }
        }
    }
    pub fn read_vec<T: std::str::FromStr>(n: usize) -> Vec<T>
    where
        <T as FromStr>::Err: Debug,
    {
        (0..n).map(|_| read::<T>()).collect::<Vec<T>>()
    }
    pub fn read_vec_sub1(n: usize) -> Vec<usize> {
        (0..n).map(|_| read::<usize>() - 1).collect::<Vec<usize>>()
    }
    pub fn read_mat<T: std::str::FromStr>(h: usize, w: usize) -> Vec<Vec<T>>
    where
        <T as FromStr>::Err: Debug,
    {
        (0..h).map(|_| read_vec::<T>(w)).collect::<Vec<Vec<T>>>()
    }
}
use procon_reader::*;
/*************************************************************************************
*************************************************************************************/

mod occupancy {
    use crate::xor_shift_64::XorShift64;
    use crate::ChangeMinMax;
    use std::collections::HashSet;
    use std::{collections::btree_map::Range, ops::RangeInclusive};
    #[derive(Clone, Copy, PartialEq)]
    pub struct OccuRange {
        d: usize,
        zrange: (usize, usize),
        yrange: (usize, usize),
        xrange: (usize, usize),
    }
    impl OccuRange {
        pub fn new(d: usize, z: usize, y: usize, x: usize) -> Self {
            Self {
                d,
                zrange: (z, z),
                yrange: (y, y),
                xrange: (x, x),
            }
        }
        pub fn expand(&mut self, z: usize, y: usize, x: usize) {
            self.zrange.0.chmin(z);
            self.zrange.1.chmax(z);
            self.yrange.0.chmin(y);
            self.yrange.1.chmax(y);
            self.xrange.0.chmin(x);
            self.xrange.1.chmax(x);
        }
        pub fn d(&self) -> usize {
            self.d
        }
        pub fn zrange(&self) -> RangeInclusive<usize> {
            self.zrange.0..=self.zrange.1
        }
        pub fn yrange(&self) -> RangeInclusive<usize> {
            self.yrange.0..=self.yrange.1
        }
        pub fn xrange(&self) -> RangeInclusive<usize> {
            self.xrange.0..=self.xrange.1
        }
        pub fn zsize(&self) -> usize {
            self.zrange.1 - self.zrange.0 + 1
        }
        pub fn ysize(&self) -> usize {
            self.yrange.1 - self.yrange.0 + 1
        }
        pub fn xsize(&self) -> usize {
            self.xrange.1 - self.xrange.0 + 1
        }
        pub fn volume(&self) -> usize {
            self.zsize() * self.ysize() * self.xsize()
        }
    }
    impl std::ops::Add<Self> for OccuRange {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret.expand(rhs.zrange.0, rhs.yrange.0, rhs.xrange.0);
            ret.expand(rhs.zrange.0, rhs.yrange.0, rhs.xrange.1);
            ret.expand(rhs.zrange.0, rhs.yrange.1, rhs.xrange.0);
            ret.expand(rhs.zrange.0, rhs.yrange.1, rhs.xrange.1);
            ret.expand(rhs.zrange.1, rhs.yrange.0, rhs.xrange.0);
            ret.expand(rhs.zrange.1, rhs.yrange.0, rhs.xrange.1);
            ret.expand(rhs.zrange.1, rhs.yrange.1, rhs.xrange.0);
            ret.expand(rhs.zrange.1, rhs.yrange.1, rhs.xrange.1);
            ret
        }
    }
    #[derive(Clone, Copy)]
    pub struct RotDir {
        pub to: usize,
        pub sign: bool,
    }
    impl RotDir {
        fn new(to: usize) -> Self {
            Self { to, sign: true }
        }
    }
    #[derive(Clone)]
    pub struct RotDir3d {
        pub dirs: Vec<RotDir>,
    }
    pub struct RotDir3dIterator {
        rots: Vec<RotDir3d>,
    }
    impl Iterator for RotDir3dIterator {
        type Item = RotDir3d;
        fn next(&mut self) -> Option<Self::Item> {
            self.rots.pop()
        }
    }
    impl RotDir3d {
        pub fn into_iter(self) -> RotDir3dIterator {
            let mut rot = RotDir3d::new();
            let mut rots = vec![];
            for _ in 0..4 {
                rots.push(rot.clone());
                rot.rot_z();
            }
            rot.rot_x();
            for _ in 0..4 {
                rots.push(rot.clone());
                rot.rot_y();
            }
            rot.rot_z();
            for _ in 0..4 {
                rots.push(rot.clone());
                rot.rot_x();
            }
            rot.rot_y();
            for _ in 0..4 {
                rots.push(rot.clone());
                rot.rot_z();
            }
            rot.rot_x();
            for _ in 0..4 {
                rots.push(rot.clone());
                rot.rot_y();
            }
            rot.rot_z();
            for _ in 0..4 {
                rots.push(rot.clone());
                rot.rot_x();
            }
            rot.rot_y();
            RotDir3dIterator { rots }
        }
        pub fn new() -> Self {
            Self {
                dirs: (0..3).map(RotDir::new).collect::<Vec<_>>(),
            }
        }
        pub fn rot_z(&mut self) {
            self.dirs.swap(1, 2);
            self.dirs[2].sign = !self.dirs[2].sign;
        }
        pub fn rot_y(&mut self) {
            self.dirs.swap(2, 0);
            self.dirs[0].sign = !self.dirs[0].sign;
        }
        pub fn rot_x(&mut self) {
            self.dirs.swap(0, 1);
            self.dirs[1].sign = !self.dirs[1].sign;
        }
        pub fn new_rand(rand: &mut XorShift64) -> Self {
            let mut rot = Self::new();
            (0..15).for_each(|_| match rand.next_usize() % 3 {
                0 => {
                    rot.rot_z();
                }
                1 => {
                    rot.rot_y();
                }
                2 => {
                    rot.rot_x();
                }
                _ => unreachable!(),
            });
            rot
        }
    }

    #[derive(Clone, Copy)]
    pub struct Safety {
        other_dir_min: usize,
        eff_size: usize,
    }
    impl From<Safety> for i64 {
        fn from(value: Safety) -> i64 {
            if value.other_dir_min <= 0 {
                value.other_dir_min as i64
            } else {
                (15 * 15 * 15 + value.eff_size) as i64
            }
        }
    }
    impl std::ops::Add<Safety> for Safety {
        type Output = Self;
        fn add(self, rhs: Safety) -> Self::Output {
            Self {
                other_dir_min: std::cmp::min(self.other_dir_min, rhs.other_dir_min),
                eff_size: self.eff_size + rhs.eff_size,
            }
        }
    }
    #[derive(Clone)]
    pub struct Occupancy {
        field: Vec<u64>,
        range: OccuRange,
        safety: Option<Safety>,
    }
    const BITWIDTH: usize = 64;
    impl Occupancy {
        fn new_empty(range: OccuRange) -> Self {
            let sz = (range.volume() + BITWIDTH - 1) / BITWIDTH;
            Self {
                field: vec![0; sz],
                range,
                safety: None,
            }
        }
        pub fn new(id_field: &[Vec<Vec<i32>>], target_id: i32, range: OccuRange) -> Self {
            let mut ret = Self::new_empty(range);
            for z in range.zrange() {
                for y in range.yrange() {
                    for x in range.xrange() {
                        let id_value = id_field[z][y][x];
                        if id_value == target_id {
                            ret.set(z, y, x);
                        }
                    }
                }
            }
            ret
        }
        fn calc_safety(&self, id_box: &[Vec<Vec<i32>>], own_id: i32) -> Safety {
            let d = id_box.len();
            let mut eff_size = 0;
            let mut other_dir_min = 1 << 60;
            for (oz, oy, ox) in self.points() {
                eff_size += 1;

                let mut other_id_y = HashSet::new();
                for y in 0..d {
                    let id = id_box[oz][y][ox];
                    if (id <= 0) || (id == own_id) {
                        continue;
                    }
                    other_id_y.insert(id);
                }
                other_dir_min.chmin(other_id_y.len());
                let mut other_id_x = HashSet::new();
                for x in 0..d {
                    let id = id_box[oz][oy][x];
                    if (id <= 0) || (id == own_id) {
                        continue;
                    }
                    other_id_x.insert(id);
                }
                other_dir_min.chmin(other_id_x.len());
            }
            Safety {
                other_dir_min,
                eff_size,
            }
        }
        pub fn get_cost(&mut self, id_box: &[Vec<Vec<i32>>], own_id: i32) -> Safety {
            if let Some(safety) = self.safety {
                return safety;
            }
            self.safety = Some(self.calc_safety(id_box, own_id));
            self.safety.unwrap()
        }
        pub fn get_range(&self) -> &OccuRange {
            &self.range
        }
        fn conv_abs3d_to_rel1d(&self, z: usize, y: usize, x: usize) -> usize {
            ((z - self.range.zrange.0) * self.range.ysize() + (y - self.range.yrange.0))
                * self.range.xsize()
                + (x - self.range.xrange.0)
        }
        pub fn set(&mut self, z: usize, y: usize, x: usize) {
            debug_assert!(z >= self.range.zrange.0);
            debug_assert!(z <= self.range.zrange.1);
            debug_assert!(y >= self.range.yrange.0);
            debug_assert!(y <= self.range.yrange.1);
            debug_assert!(x >= self.range.xrange.0);
            debug_assert!(x <= self.range.xrange.1);
            let idx = self.conv_abs3d_to_rel1d(z, y, x);
            let div = idx / BITWIDTH;
            let rem = idx % BITWIDTH;
            self.field[div] |= 1 << rem;
        }
        #[allow(clippy::type_complexity)]
        pub fn points(&self) -> Vec<(usize, usize, usize)> {
            let mut points = vec![];
            for z in self.range.zrange() {
                for y in self.range.yrange() {
                    for x in self.range.xrange().filter(|&x| self.get(z, y, x)) {
                        points.push((z, y, x));
                    }
                }
            }
            points
        }
        pub fn eff_size(&self) -> usize {
            let ret = self.field.iter().map(|x| x.count_ones()).sum::<u32>() as usize;
            debug_assert!(ret == self.points().len());
            ret
        }
        pub fn get(&self, z: usize, y: usize, x: usize) -> bool {
            let idx = self.conv_abs3d_to_rel1d(z, y, x);
            let div = idx / BITWIDTH;
            let rem = idx % BITWIDTH;
            ((self.field[div] >> rem) & 1) != 0
        }
        fn get_rel(&self, rz: usize, ry: usize, rx: usize) -> bool {
            let range = self.get_range();
            let idx = (rz * range.ysize() + ry) * range.xsize() + rx;
            let div = idx / BITWIDTH;
            let rem = idx % BITWIDTH;
            ((self.field[div] >> rem) & 1) != 0
        }
        fn rot_z(&mut self) {
            self.rot_z_dir(true)
        }
        fn rot_z_dir(&mut self, dir: bool) {
            let mut range = self.range;
            let org_volume = range.volume();
            std::mem::swap(&mut range.yrange, &mut range.xrange);
            if dir {
                std::mem::swap(&mut range.xrange.0, &mut range.xrange.1);
                range.xrange.0 = range.d - 1 - range.xrange.0;
                range.xrange.1 = range.d - 1 - range.xrange.1;
            } else {
                std::mem::swap(&mut range.yrange.0, &mut range.yrange.1);
                range.yrange.0 = range.d - 1 - range.yrange.0;
                range.yrange.1 = range.d - 1 - range.yrange.1;
            }
            debug_assert!(org_volume == range.volume());
            let mut ret = Self::new_empty(range);
            for z0 in self.range.zrange() {
                let z1 = ret.range.zrange.0 + (z0 - self.range.zrange.0);
                for y0 in self.range.yrange() {
                    let x1 = if dir { self.range.d - 1 - y0 } else { y0 };
                    for x0 in self.range.xrange() {
                        let y1 = if dir { x0 } else { self.range.d - 1 - x0 };
                        if self.get(z0, y0, x0) {
                            ret.set(z1, y1, x1);
                        }
                    }
                }
            }
            *self = ret;
        }
        fn rot_y(&mut self) {
            self.rot_y_dir(true)
        }
        fn rot_y_dir(&mut self, dir: bool) {
            let mut range = self.range;
            let org_volume = range.volume();
            std::mem::swap(&mut range.zrange, &mut range.xrange);
            if dir {
                std::mem::swap(&mut range.xrange.0, &mut range.xrange.1);
                range.xrange.0 = range.d - 1 - range.xrange.0;
                range.xrange.1 = range.d - 1 - range.xrange.1;
            } else {
                std::mem::swap(&mut range.zrange.0, &mut range.zrange.1);
                range.zrange.0 = range.d - 1 - range.zrange.0;
                range.zrange.1 = range.d - 1 - range.zrange.1;
            }
            debug_assert!(org_volume == range.volume());
            let mut ret = Self::new_empty(range);
            for z0 in self.range.zrange() {
                let x1 = if dir { self.range.d - 1 - z0 } else { z0 };
                for y0 in self.range.yrange() {
                    let y1 = ret.range.yrange.0 + (y0 - self.range.yrange.0);
                    for x0 in self.range.xrange() {
                        let z1 = if dir { x0 } else { self.range.d - 1 - x0 };
                        if self.get(z0, y0, x0) {
                            ret.set(z1, y1, x1);
                        }
                    }
                }
            }
            *self = ret;
        }
        fn rot_x(&mut self) {
            self.rot_x_dir(true)
        }
        fn rot_x_dir(&mut self, dir: bool) {
            let mut range = self.range;
            let org_volume = range.volume();
            std::mem::swap(&mut range.zrange, &mut range.yrange);
            if dir {
                std::mem::swap(&mut range.yrange.0, &mut range.yrange.1);
                range.yrange.0 = range.d - 1 - range.yrange.0;
                range.yrange.1 = range.d - 1 - range.yrange.1;
            } else {
                std::mem::swap(&mut range.zrange.0, &mut range.zrange.1);
                range.zrange.0 = range.d - 1 - range.zrange.0;
                range.zrange.1 = range.d - 1 - range.zrange.1;
            }
            debug_assert!(org_volume == range.volume());
            let mut ret = Self::new_empty(range);
            for z0 in self.range.zrange() {
                let y1 = if dir { self.range.d - 1 - z0 } else { z0 };
                for y0 in self.range.yrange() {
                    let z1 = if dir { y0 } else { self.range.d - 1 - y0 };
                    for x0 in self.range.xrange() {
                        let x1 = ret.range.xrange.0 + (x0 - self.range.xrange.0);
                        if self.get(z0, y0, x0) {
                            ret.set(z1, y1, x1);
                        }
                    }
                }
            }
            *self = ret;
        }
        fn merge_match2(&self, others: &[&Self], rot10: &RotDir3d) -> bool {
            debug_assert!(self.eff_size() == others[0].eff_size() + others[1].eff_size());
            let mrange = *others[0].get_range() + *others[1].get_range();
            let range0 = self.get_range();
            let size0 = (0..3)
                .map(|d| match rot10.dirs[d].to {
                    0 => range0.zsize(),
                    1 => range0.ysize(),
                    2 => range0.xsize(),
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>();
            if (mrange.zsize() != size0[0])
                || (mrange.ysize() != size0[1])
                || (mrange.xsize() != size0[2])
            {
                return false;
            }
            for other in others {
                let range1 = other.get_range();
                let mut rzyx0 = [0; 3];
                for rz1 in 0..range1.zsize() {
                    rzyx0[rot10.dirs[0].to] = if rot10.dirs[0].sign {
                        rz1 + (range1.zrange.0 - mrange.zrange.0)
                    } else {
                        mrange.zsize() - 1 - (rz1 + (range1.zrange.0 - mrange.zrange.0))
                    };
                    for ry1 in 0..range1.ysize() {
                        rzyx0[rot10.dirs[1].to] = if rot10.dirs[1].sign {
                            ry1 + (range1.yrange.0 - mrange.yrange.0)
                        } else {
                            mrange.ysize() - 1 - (ry1 + (range1.yrange.0 - mrange.yrange.0))
                        };
                        for rx1 in 0..range1.xsize() {
                            rzyx0[rot10.dirs[2].to] = if rot10.dirs[2].sign {
                                rx1 + (range1.xrange.0 - mrange.xrange.0)
                            } else {
                                mrange.xsize() - 1 - (rx1 + (range1.xrange.0 - mrange.xrange.0))
                            };
                            if other.get_rel(rz1, ry1, rx1)
                                != self.get_rel(rzyx0[0], rzyx0[1], rzyx0[2])
                            {
                                return false;
                            }
                        }
                    }
                }
            }
            true
        }
        fn move_match2(&self, other: &Self, rot01: &RotDir3d) -> bool {
            let range0 = self.get_range();
            let range1 = other.get_range();
            let range1 = (0..3)
                .map(|d| match rot01.dirs[d].to {
                    0 => range1.zsize(),
                    1 => range1.ysize(),
                    2 => range1.xsize(),
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>();
            if (range0.zsize() != range1[0])
                || (range0.ysize() != range1[1])
                || (range0.xsize() != range1[2])
            {
                return false;
            }
            let mut rzyx1 = [0; 3];
            for rz0 in 0..range0.zsize() {
                rzyx1[rot01.dirs[0].to] = if rot01.dirs[0].sign {
                    rz0
                } else {
                    range0.zsize() - 1 - rz0
                };
                for ry0 in 0..range0.ysize() {
                    rzyx1[rot01.dirs[1].to] = if rot01.dirs[1].sign {
                        ry0
                    } else {
                        range0.ysize() - 1 - ry0
                    };
                    for rx0 in 0..range0.xsize() {
                        rzyx1[rot01.dirs[2].to] = if rot01.dirs[2].sign {
                            rx0
                        } else {
                            range0.xsize() - 1 - rx0
                        };
                        if self.get_rel(rz0, ry0, rx0)
                            != other.get_rel(rzyx1[0], rzyx1[1], rzyx1[2])
                        {
                            return false;
                        }
                    }
                }
            }
            true
        }
        fn rot_z_match(&self, other: &Self) -> bool {
            let mut re = other.clone();
            if self.move_match(&re) {
                return true;
            }
            for _ in 0..3 {
                re.rot_z();
                if self.move_match(&re) {
                    return true;
                }
            }
            false
        }
        fn rot_z_match2(&self, other: &Self, rot01: &mut RotDir3d) -> bool {
            if self.move_match2(other, rot01) {
                return true;
            }
            for _ in 0..3 {
                rot01.rot_z();
                if self.move_match2(other, rot01) {
                    return true;
                }
            }
            false
        }
        fn rot_match2(&self, other: &Self) -> bool {
            if self.eff_size() != other.eff_size() {
                return false;
            }
            let mut rot01 = RotDir3d::new();
            for _ in 0..4 {
                if self.move_match2(other, &rot01) {
                    return true;
                }
                rot01.rot_z();
            }
            rot01.rot_x();
            for _ in 0..4 {
                if self.move_match2(other, &rot01) {
                    return true;
                }
                rot01.rot_y();
            }
            rot01.rot_z();
            for _ in 0..4 {
                if self.move_match2(other, &rot01) {
                    return true;
                }
                rot01.rot_x();
            }
            rot01.rot_y();
            for _ in 0..4 {
                if self.move_match2(other, &rot01) {
                    return true;
                }
                rot01.rot_z();
            }
            rot01.rot_x();
            for _ in 0..4 {
                if self.move_match2(other, &rot01) {
                    return true;
                }
                rot01.rot_y();
            }
            rot01.rot_z();
            for _ in 0..4 {
                if self.move_match2(other, &rot01) {
                    return true;
                }
                rot01.rot_x();
            }
            rot01.rot_y();
            false
        }
        pub fn rot_merge_match2(&self, others: &[&Self]) -> bool {
            if self.eff_size() != others[0].eff_size() + others[1].eff_size() {
                return false;
            }
            let mut rot10 = RotDir3d::new();
            for _ in 0..4 {
                if self.merge_match2(others, &rot10) {
                    return true;
                }
                rot10.rot_z();
            }
            rot10.rot_x();
            for _ in 0..4 {
                if self.merge_match2(others, &rot10) {
                    return true;
                }
                rot10.rot_y();
            }
            rot10.rot_z();
            for _ in 0..4 {
                if self.merge_match2(others, &rot10) {
                    return true;
                }
                rot10.rot_x();
            }
            rot10.rot_y();
            for _ in 0..4 {
                if self.merge_match2(others, &rot10) {
                    return true;
                }
                rot10.rot_z();
            }
            rot10.rot_x();
            for _ in 0..4 {
                if self.merge_match2(others, &rot10) {
                    return true;
                }
                rot10.rot_y();
            }
            rot10.rot_z();
            for _ in 0..4 {
                if self.merge_match2(others, &rot10) {
                    return true;
                }
                rot10.rot_x();
            }
            rot10.rot_y();
            false
        }
        fn rot_match(&self, other: &Self) -> bool {
            let mut ret = false;
            let mut re = other.clone();
            if self.rot_z_match(&re) {
                ret = true;
            }
            for dir in 0..5 {
                if dir % 2 == 0 {
                    re.rot_x();
                } else {
                    re.rot_y();
                }
                if self.rot_z_match(&re) {
                    ret = true;
                }
            }
            assert!(ret == self.rot_match2(other));
            ret
        }
        pub fn move_match(&self, other: &Self) -> bool {
            if self.range.zsize() != other.range.zsize() {
                debug_assert!(!self.move_match2(other, &RotDir3d::new()));
                return false;
            }
            if self.range.ysize() != other.range.ysize() {
                debug_assert!(!self.move_match2(other, &RotDir3d::new()));
                return false;
            }
            if self.range.xsize() != other.range.xsize() {
                debug_assert!(!self.move_match2(other, &RotDir3d::new()));
                return false;
            }
            if self.field != other.field {
                debug_assert!(!self.move_match2(other, &RotDir3d::new()));
                return false;
            }
            debug_assert!(self.move_match2(other, &RotDir3d::new()));
            true
        }
        pub fn write_id(&self, id_box: &mut [Vec<Vec<i32>>], target_id: i32) {
            for z in self.range.zrange() {
                for y in self.range.yrange() {
                    for x in self.range.xrange() {
                        if !self.get(z, y, x) {
                            continue;
                        }
                        id_box[z][y][x] = target_id;
                    }
                }
            }
        }
        pub fn to_units(&self) -> Vec<Self> {
            let d = self.get_range().d();
            self.points()
                .into_iter()
                .map(|(z, y, x)| -> Occupancy {
                    let mut occ = Occupancy::new_empty(OccuRange::new(d, z, y, x));
                    occ.set(z, y, x);
                    occ
                })
                .collect::<Vec<_>>()
        }
    }
    impl PartialEq for Occupancy {
        fn eq(&self, other: &Self) -> bool {
            let ret = self.rot_match2(other);
            if cfg!(debug_assertions) && ret {
                debug_assert!(self.get_range().volume() == other.get_range().volume());
                debug_assert!(self.eff_size() == other.eff_size());
            }
            ret
        }
    }
    impl std::ops::Add<Self> for Occupancy {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            let range = self.range + rhs.range;
            let mut ret = Self::new_empty(range);
            for (z, y, x) in self.points() {
                ret.set(z, y, x);
            }
            for (z, y, x) in rhs.points() {
                ret.set(z, y, x);
            }
            debug_assert!(ret.eff_size() == self.eff_size() + rhs.eff_size());
            ret
        }
    }

    #[cfg(test)]
    mod tests {
        use super::{OccuRange, Occupancy};
        use crate::XorShift64;
        const TEST_LOOP: usize = 10000;
        fn create_occ(
            d: usize,
            zsize: usize,
            ysize: usize,
            xsize: usize,
            rand: &mut XorShift64,
        ) -> Occupancy {
            let range = OccuRange::new(d, zsize, ysize, xsize);
            let mut occ = Occupancy::new_empty(range);
            for z in range.zrange.0..=range.zrange.1 {
                for y in range.yrange.0..=range.yrange.1 {
                    for x in range.xrange.0..=range.xrange.1 {
                        if rand.next_usize() % 2 == 0 {
                            occ.set(z, y, x);
                        }
                    }
                }
            }
            occ
        }
        #[test]
        fn test_rot_z() {
            let mut rand = XorShift64::new();
            let d = 14;
            for _ in 0..TEST_LOOP {
                let zsize = 1 + rand.next_usize() % (d - 1);
                let ysize = 1 + rand.next_usize() % (d - 1);
                let xsize = 1 + rand.next_usize() % (d - 1);
                let occ = create_occ(d, zsize, ysize, xsize, &mut rand);
                for c in 0..4 {
                    let mut ref0 = occ.clone();
                    let mut ref1 = occ.clone();
                    for _ in 0..c {
                        ref0.rot_z_dir(true);
                    }
                    for _ in 0..4 - c {
                        ref1.rot_z_dir(false);
                    }
                    assert!(ref0.move_match(&ref1));
                }
            }
        }
        #[test]
        fn test_rot_y() {
            let mut rand = XorShift64::new();
            let d = 14;
            for _ in 0..TEST_LOOP {
                let zsize = 1 + rand.next_usize() % (d - 1);
                let ysize = 1 + rand.next_usize() % (d - 1);
                let xsize = 1 + rand.next_usize() % (d - 1);
                let occ = create_occ(d, zsize, ysize, xsize, &mut rand);
                for c in 0..4 {
                    let mut ref0 = occ.clone();
                    let mut ref1 = occ.clone();
                    for _ in 0..c {
                        ref0.rot_y_dir(true);
                    }
                    for _ in 0..4 - c {
                        ref1.rot_y_dir(false);
                    }
                    assert!(ref0.move_match(&ref1));
                }
            }
        }
        #[test]
        fn test_rot_x() {
            let mut rand = XorShift64::new();
            let d = 14;
            for _ in 0..TEST_LOOP {
                let zsize = 1 + rand.next_usize() % (d - 1);
                let ysize = 1 + rand.next_usize() % (d - 1);
                let xsize = 1 + rand.next_usize() % (d - 1);
                let occ = create_occ(d, zsize, ysize, xsize, &mut rand);
                for c in 0..4 {
                    let mut ref0 = occ.clone();
                    let mut ref1 = occ.clone();
                    for _ in 0..c {
                        ref0.rot_x_dir(true);
                    }
                    for _ in 0..4 - c {
                        ref1.rot_x_dir(false);
                    }
                    assert!(ref0.move_match(&ref1));
                }
            }
        }
        #[test]
        fn test_rot() {
            let mut rand = XorShift64::new();
            let d = 14;
            for _ in 0..TEST_LOOP {
                let zsize = 1 + rand.next_usize() % (d - 1);
                let ysize = 1 + rand.next_usize() % (d - 1);
                let xsize = 1 + rand.next_usize() % (d - 1);
                let occ = create_occ(d, zsize, ysize, xsize, &mut rand);
                let ref0 = occ.clone();
                let mut ref1 = occ.clone();
                for _ in 0..100 {
                    match rand.next_u64() % 3 {
                        0 => {
                            ref1.rot_z();
                        }
                        1 => {
                            ref1.rot_y();
                        }
                        2 => {
                            ref1.rot_x();
                        }
                        _ => unreachable!(),
                    }
                    assert!(ref0.rot_match(&ref1));
                }
            }
        }
        fn test_rot2() {
            let mut rand = XorShift64::new();
            let d = 14;
            for _ in 0..TEST_LOOP {
                let zsize = 1 + rand.next_usize() % (d - 1);
                let ysize = 1 + rand.next_usize() % (d - 1);
                let xsize = 1 + rand.next_usize() % (d - 1);
                let ref0 = create_occ(d, zsize, ysize, xsize, &mut rand);
                let mut ref1 = {
                    let mut ref1 = create_occ(d, zsize, ysize, xsize, &mut rand);
                    while ref0.move_match(&ref1) {
                        ref1 = create_occ(d, zsize, ysize, xsize, &mut rand);
                    }
                    ref1
                };
                for _ in 0..100 {
                    match rand.next_u64() % 3 {
                        0 => {
                            ref1.rot_z();
                        }
                        1 => {
                            ref1.rot_y();
                        }
                        2 => {
                            ref1.rot_x();
                        }
                        _ => unreachable!(),
                    }
                    assert!(!ref0.rot_match(&ref1));
                }
            }
        }
        #[test]
        fn test_volume1() {
            let d = 5;
            let or0 = OccuRange::new(d, 0, 0, 0);
            let or1 = OccuRange::new(d, 1, 1, 1);
            let mut o0 = Occupancy::new_empty(or0);
            let mut o1 = Occupancy::new_empty(or1);
            o0.set(0, 0, 0);
            o1.set(1, 1, 1);
            assert!(o0 == o1);
        }
    }
}
mod state {
    use crate::{
        flow::Flow,
        occupancy::{OccuRange, Occupancy, RotDir3d},
        xor_shift_64::XorShift64,
        ChangeMinMax, CoordinateCompress, MoveDelta,
    };
    use core::num;
    use std::collections::{BTreeMap, BTreeSet, VecDeque};
    use std::time::Instant;
    pub struct Silhouette {
        pub zx: Vec<Vec<bool>>,
        pub zy: Vec<Vec<bool>>,
    }
    impl Silhouette {
        pub fn new(d: usize) -> Self {
            use crate::procon_reader::*;
            let zx = (0..d)
                .map(|_| {
                    read::<String>()
                        .chars()
                        .map(|c| c == '1')
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let zy = (0..d)
                .map(|_| {
                    read::<String>()
                        .chars()
                        .map(|c| c == '1')
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            Self { zx, zy }
        }
    }
    struct BfsResult {
        dist_count: usize,
        dist01: Vec<Vec<Vec<Option<(usize, usize, usize)>>>>,
    }
    impl BfsResult {
        fn new(d: usize) -> Self {
            Self {
                dist_count: 0,
                dist01: vec![vec![vec![None; d]; d]; d],
            }
        }
    }
    #[derive(Clone)]
    pub struct State {
        pub id_field: Vec<Vec<Vec<Vec<i32>>>>,
    }
    const DELTAS: [(i32, i32, i32); 6] = [
        (0, 0, 1),
        (0, 0, -1),
        (0, 1, 0),
        (0, -1, 0),
        (1, 0, 0),
        (-1, 0, 0),
    ];
    impl State {
        pub fn new(silhouettes: &[Silhouette], d: usize) -> Self {
            let mut id_field = vec![vec![vec![vec![0; d]; d]; d]; 2];
            let mut cnt = 0;
            for (silhouette, id_box) in silhouettes.iter().zip(id_field.iter_mut()) {
                for (z, id_plane) in id_box.iter_mut().enumerate() {
                    for y in (0..d).filter(|&y| silhouette.zy[z][y]) {
                        for x in (0..d).filter(|&x| silhouette.zx[z][x]) {
                            cnt += 1;
                            id_plane[y][x] = cnt;
                        }
                    }
                }
            }
            Self { id_field }
        }
        pub fn connect_isolated_blocks(&mut self) {
            let d = self.id_field[0].len();
            let to_1dim = |z: usize, y: usize, x: usize| ((z * d) + y) * d + x;
            let to_3dim = |i: usize| (i / (d * d), (i % (d * d)) / d, i % d);
            for id_box in self.id_field.iter_mut() {
                let src = d * d * d;
                let dst = src + 1;
                let mut mf = Flow::new(dst + 1);
                for z in 0..d {
                    for y in 0..d {
                        for x in 0..d {
                            debug_assert!(z == to_3dim(to_1dim(z, y, x)).0);
                            debug_assert!(y == to_3dim(to_1dim(z, y, x)).1);
                            debug_assert!(x == to_3dim(to_1dim(z, y, x)).2);
                            let id_val = id_box[z][y][x];
                            if id_val <= 0 {
                                continue;
                            }
                            if !Self::is_isolated(id_box, (z, y, x)) {
                                continue;
                            }
                            // can set
                            if (z + y + x) % 2 == 1 {
                                mf.add_edge(to_1dim(z, y, x), dst, 1);
                            } else {
                                mf.add_edge(src, to_1dim(z, y, x), 1);
                                for &(dz, dy, dx) in DELTAS.iter() {
                                    if let Some(nz) = z.move_delta(dz, 0, d - 1) {
                                        if let Some(ny) = y.move_delta(dy, 0, d - 1) {
                                            if let Some(nx) = x.move_delta(dx, 0, d - 1) {
                                                let nid = id_box[nz][ny][nx];
                                                if nid <= 0 {
                                                    continue;
                                                }
                                                if !Self::is_isolated(id_box, (nz, ny, nx)) {
                                                    continue;
                                                }
                                                debug_assert!((nz + ny + nx) % 2 == 1);
                                                debug_assert!(id_box[nz][ny][nx] > 0);
                                                debug_assert!(id_box[z][y][x] > 0);
                                                mf.add_edge(
                                                    to_1dim(z, y, x),
                                                    to_1dim(nz, ny, nx),
                                                    1,
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                if mf.max_flow(src, dst) == 0 {
                    continue;
                }
                for z in 0..d {
                    for y in 0..d {
                        for x in 0..d {
                            let id_val = id_box[z][y][x];
                            if id_val <= 0 {
                                continue;
                            }
                            if !Self::is_isolated(id_box, (z, y, x)) {
                                continue;
                            }
                            if (z + y + x) % 2 == 0 {
                                for e in mf.g[to_1dim(z, y, x)].iter() {
                                    if e.to >= d * d * d {
                                        continue;
                                    }
                                    if e.flow == 0 {
                                        continue;
                                    }
                                    let (nz, ny, nx) = to_3dim(e.to);
                                    let nid = id_box[nz][ny][nx];
                                    debug_assert!(nid > 0);
                                    debug_assert!(nz < d);
                                    debug_assert!(ny < d);
                                    debug_assert!(nx < d);
                                    debug_assert!(
                                        (z as i32 - nz as i32).abs()
                                            + (y as i32 - ny as i32).abs()
                                            + (x as i32 - nx as i32).abs()
                                            <= 1
                                    );
                                    id_box[nz][ny][nx] = id_val;
                                }
                            }
                        }
                    }
                }
            }
        }
        pub fn refine(state: &mut State) -> bool {
            let mut occs = state.positive_occupancies();
            // split parity, and search nearest pair.
            let mut splits = vec![]; // [sil, grp, num]
            let mut all_nears = vec![]; // [sil, all_occ, near-occ]
            for occs in &occs {
                let (split, near) = Self::split_to_binary_graph(occs);
                splits.push(split);
                all_nears.push(near);
            }
            // create compression dictionay.
            let mut encs = vec![vec![]; 2]; // [sil, grp]
            for si in 0..2 {
                for grp in 0..2 {
                    encs[si].push(splits[si][grp].compress_encoder());
                }
            }
            // build merge memo.
            let mut merge_occs: Vec<Occupancy> = vec![];
            let mut merge_memo: Vec<Vec<Vec<(usize, usize)>>> = vec![]; // (oi0, oi1) for [merge_num, sil, near_pair_num]
            for si in 0..2 {
                for &oi0 in &splits[si][0] {
                    debug_assert!(encs[si][0].contains_key(&oi0));
                    let occ0 = &occs[si][oi0];
                    //let e0 = encs[si][0][&oi0];
                    for &oi1 in &all_nears[si][oi0] {
                        if !encs[si][1].contains_key(&oi1) {
                            continue;
                        };
                        let occ1 = &occs[si][oi1];
                        //let e1 = encs[si][1][&oi1];
                        let mut is_new = true;
                        for (mi, al_merge_occ) in merge_occs.iter().enumerate() {
                            if al_merge_occ.rot_merge_match2(&[occ0, occ1]) {
                                if si == 0 {
                                    merge_memo[mi][si].push((oi0, oi1));
                                } else {
                                    merge_memo[mi][si].push((oi1, oi0));
                                }
                                is_new = false;
                                break;
                            }
                        }
                        if is_new {
                            let merge_occ = occ0.clone() + occ1.clone();
                            merge_occs.push(merge_occ);
                            if si == 0 {
                                merge_memo.push(vec![vec![(oi0, oi1); 1], vec![]]);
                            } else {
                                merge_memo.push(vec![vec![], vec![(oi1, oi0); 1]]);
                            }
                        }
                    }
                }
            }
            debug_assert!(merge_memo.iter().all(|memo| memo.len() == 2));
            debug_assert!(merge_occs.len() == merge_memo.len());
            for mi in (0..merge_memo.len()).rev() {
                if mi >= merge_memo.len() {
                    continue;
                }
                if merge_memo[mi][0].is_empty() || merge_memo[mi][1].is_empty() {
                    merge_occs.remove(mi);
                    merge_memo.remove(mi);
                }
            }
            if merge_memo.is_empty() {
                return false;
            }
            debug_assert!(
                merge_occs.iter().map(|occ| occ.eff_size()).max().unwrap()
                    <= state
                        .id_field
                        .iter()
                        .map(|id_box| id_box
                            .iter()
                            .map(|id_plane| id_plane
                                .iter()
                                .map(|id_line| id_line.iter().filter(|&&id_val| id_val > 0).count())
                                .sum::<usize>())
                            .sum::<usize>())
                        .sum::<usize>()
            );
            if cfg!(debug_assertions) {
                for memo in &merge_memo {
                    for (oi00, oi01) in memo[0].iter().copied() {
                        for (oi10, oi11) in memo[1].iter().copied() {
                            let occ00 = occs[0][oi00].clone();
                            let occ01 = occs[0][oi01].clone();
                            let occ10 = occs[1][oi10].clone();
                            let occ11 = occs[1][oi11].clone();
                            let occ0 = occ00 + occ01;
                            let occ1 = occ10 + occ11;
                            debug_assert!(occ0.points().len() == occ1.points().len());
                            debug_assert!(occ0 == occ1);
                        }
                    }
                }
            }
            // build flow graph.
            let num_even = (0..2).map(|si| splits[si][0].len()).collect::<Vec<_>>();
            let num_pair = (0..2)
                .map(|si| merge_memo.iter().map(|sils| sils[si].len()).sum::<usize>())
                .collect::<Vec<_>>();
            let num_merge = merge_occs.len();
            let src = num_even.iter().sum::<usize>() + num_pair.iter().sum::<usize>() + num_merge;
            let dst = src + 1;
            let mut maxf = Flow::new(dst + 1);
            let mut minf = Flow::new(dst + 1);
            {
                for i in 0..num_even[0] {
                    minf.add_cost_edge(src, i, 1, 0);
                    maxf.add_edge(src, i, 1);
                }
            }
            {
                let mut p0 = num_even[0];
                for memo in &merge_memo {
                    for &(oi00, oi01) in &memo[0] {
                        debug_assert!(encs[0][0].contains_key(&oi00));
                        debug_assert!(encs[0][1].contains_key(&oi01));
                        let ei00 = encs[0][0][&oi00];
                        minf.add_cost_edge(ei00, p0, 1, 0);
                        maxf.add_edge(ei00, p0, 1);
                        p0 += 1;
                    }
                }
                debug_assert!(p0 == num_even[0] + num_pair[0]);
            }
            {
                let mut p0 = num_even[0];
                for (mi, memo) in merge_memo.iter().enumerate() {
                    for &(oi00, oi01) in &memo[0] {
                        debug_assert!(encs[0][0].contains_key(&oi00));
                        debug_assert!(encs[0][1].contains_key(&oi01));
                        let cost0 = {
                            let occ = &mut occs[0][oi00];
                            let (z, y, x) = occ.points()[0];
                            let id = state.id_field[0][z][y][x];
                            debug_assert!(id > 0);
                            occ.get_cost(&state.id_field[0], id)
                        };
                        let cost1 = {
                            let occ = &mut occs[0][oi01];
                            let (z, y, x) = occ.points()[0];
                            let id = state.id_field[0][z][y][x];
                            debug_assert!(id > 0);
                            occ.get_cost(&state.id_field[0], id)
                        };
                        let cost = cost0 + cost1;
                        minf.add_cost_edge(p0, num_even[0] + num_pair[0] + mi, 1, cost.into());
                        maxf.add_edge(p0, num_even[0] + num_pair[0] + mi, 1);
                        p0 += 1;
                    }
                }
                debug_assert!(p0 == num_even[0] + num_pair[0]);
            }
            // center
            {
                let mut p1 = num_even[0] + num_pair[0] + num_merge;
                for (mi, memo) in merge_memo.iter().enumerate() {
                    for &(oi11, oi10) in &memo[1] {
                        debug_assert!(encs[1][0].contains_key(&oi10));
                        debug_assert!(encs[1][1].contains_key(&oi11));
                        let cost0 = {
                            let occ = &mut occs[1][oi10];
                            let (z, y, x) = occ.points()[0];
                            let id = state.id_field[1][z][y][x];
                            debug_assert!(id > 0);
                            occ.get_cost(&state.id_field[1], id)
                        };
                        let cost1 = {
                            let occ = &mut occs[1][oi11];
                            let (z, y, x) = occ.points()[0];
                            let id = state.id_field[1][z][y][x];
                            debug_assert!(id > 0);
                            occ.get_cost(&state.id_field[1], id)
                        };
                        let cost = cost0 + cost1;
                        minf.add_cost_edge(num_even[0] + num_pair[0] + mi, p1, 1, cost.into());
                        maxf.add_edge(num_even[0] + num_pair[0] + mi, p1, 1);
                        p1 += 1;
                    }
                }
                debug_assert!(p1 == num_even[0] + num_pair[0] + num_merge + num_pair[1]);
            }
            {
                let mut p1 = num_even[0] + num_pair[0] + num_merge;
                for memo in &merge_memo {
                    for &(oi11, oi10) in &memo[1] {
                        debug_assert!(encs[1][0].contains_key(&oi10));
                        debug_assert!(encs[1][1].contains_key(&oi11));
                        let ei10 = encs[1][0][&oi10];
                        minf.add_cost_edge(
                            p1,
                            num_even[0] + num_pair[0] + num_merge + num_pair[1] + ei10,
                            1,
                            0,
                        );
                        maxf.add_edge(
                            p1,
                            num_even[0] + num_pair[0] + num_merge + num_pair[1] + ei10,
                            1,
                        );
                        p1 += 1;
                    }
                }
                debug_assert!(p1 == num_even[0] + num_pair[0] + num_merge + num_pair[1]);
            }
            {
                for ei10 in 0..num_even[1] {
                    minf.add_cost_edge(
                        num_even[0] + num_pair[0] + num_merge + num_pair[1] + ei10,
                        dst,
                        1,
                        0,
                    );
                    maxf.add_edge(
                        num_even[0] + num_pair[0] + num_merge + num_pair[1] + ei10,
                        dst,
                        1,
                    );
                }
            }
            let flow = maxf.max_flow(src, dst);
            if flow == 0 {
                return false;
            }
            assert!(minf
                .min_cost_flow(src, dst, std::cmp::max(1, flow - 2))
                .is_some());

            // flow any.
            let mut id_cnt = 1;
            for (id_box, occs) in state.id_field.iter_mut().zip(occs.iter()) {
                for occ in occs {
                    occ.write_id(id_box, id_cnt);
                    id_cnt += 1;
                }
            }
            let mut remains = occs
                .iter()
                .map(|occs| vec![true; occs.len()])
                .collect::<Vec<Vec<bool>>>();
            let mut p0_base = 0;
            let mut p1_base = 0;
            for (mi, memo) in merge_memo.iter().enumerate() {
                let vmi = num_even[0] + num_pair[0] + mi;
                for to1 in minf.g[vmi].iter() {
                    if to1.to < vmi {
                        continue;
                    }
                    if to1.flow == 0 {
                        continue;
                    }
                    // flows to sil 1;
                    let p1 = to1.to - (num_even[0] + num_pair[0] + num_merge) - p1_base;
                    let (oi11, oi10) = memo[1][p1];
                    if (!remains[1][oi10]) || (!remains[1][oi11]) {
                        continue;
                    }
                    for from0 in minf.g[vmi].iter() {
                        if from0.to > vmi {
                            continue;
                        }
                        if minf.g[from0.to][from0.rev_idx].flow == 0 {
                            continue;
                        }
                        if minf.g[from0.to][from0.rev_idx].to != vmi {
                            continue;
                        }
                        let p0 = from0.to - num_even[0] - p0_base;
                        let (oi00, oi01) = memo[0][p0];
                        if (!remains[0][oi00]) || (!remains[0][oi01]) {
                            continue;
                        }
                        debug_assert!(
                            occs[0][oi00].clone() + occs[0][oi01].clone()
                                == occs[1][oi10].clone() + occs[1][oi11].clone()
                        );
                        // FOUND MATCH!!!!
                        remains[0][oi00] = false;
                        remains[0][oi01] = false;
                        remains[1][oi10] = false;
                        remains[1][oi11] = false;
                        let (z0, y0, x0) = occs[0][oi00].points()[0];
                        let merge_id0 = state.id_field[0][z0][y0][x0];
                        occs[0][oi01].write_id(&mut state.id_field[0], merge_id0);
                        let (z1, y1, x1) = occs[1][oi10].points()[0];
                        let merge_id1 = state.id_field[1][z1][y1][x1];
                        occs[1][oi11].write_id(&mut state.id_field[1], merge_id1);
                        break;
                    }
                }
                p0_base += memo[0].len();
                p1_base += memo[1].len();
            }
            true
        }
        fn split_to_binary_graph(occs: &[Occupancy]) -> (Vec<Vec<usize>>, Vec<BTreeSet<usize>>) {
            let d = occs[0].get_range().d();
            debug_assert!(occs.iter().all(|occ| occ.get_range().d() == d));
            let mut id_box = vec![vec![vec![0i32; d]; d]; d];
            for (oi, occ) in occs.iter().enumerate() {
                for (z, y, x) in occ.points() {
                    let id_val = oi as i32 + 1;
                    id_box[z][y][x] = id_val;
                }
            }

            let mut dist = vec![None; occs.len()]; // oi, dist
            let mut near = vec![BTreeSet::new(); occs.len()];
            for (oi, _occ) in occs.iter().enumerate() {
                if dist[oi].is_some() {
                    continue;
                }
                let mut que = VecDeque::new(); // oi
                que.push_back(oi);
                dist[oi] = Some(0);
                while let Some(oi0) = que.pop_front() {
                    let occ0 = &occs[oi0];
                    let d0 = dist[oi0].unwrap();
                    let d1 = d0 + 1;
                    // scan near
                    for (z0, y0, x0) in occ0.points() {
                        let id0 = id_box[z0][y0][x0];
                        debug_assert!(id0 == oi0 as i32 + 1);
                        for &(dz, dy, dx) in DELTAS.iter() {
                            if let Some(z1) = z0.move_delta(dz, 0, d - 1) {
                                if let Some(y1) = y0.move_delta(dy, 0, d - 1) {
                                    if let Some(x1) = x0.move_delta(dx, 0, d - 1) {
                                        let id1 = id_box[z1][y1][x1];
                                        if id1 <= 0 || id1 == id0 {
                                            continue;
                                        }
                                        let oi1 = id1 as usize - 1;
                                        near[oi0].insert(oi1);
                                        near[oi1].insert(oi0);
                                        if dist[oi1].chmin(d1) {
                                            que.push_back(oi1);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            let mut ois = vec![vec![]; 2];
            for (oi, dist) in dist.into_iter().enumerate() {
                ois[dist.unwrap() % 2].push(oi);
            }
            debug_assert!(ois.iter().map(|ois| ois.len()).sum::<usize>() == occs.len());
            (ois, near)
        }
        pub fn positive_occupancies(&self) -> Vec<Vec<Occupancy>> {
            let d = self.id_field[0].len();
            let mut ret: Vec<Vec<Occupancy>> = vec![];
            for id_box in self.id_field.iter() {
                let mut ranges: BTreeMap<i32, OccuRange> = BTreeMap::new();
                for (z, id_plane) in id_box.iter().enumerate() {
                    for (y, id_line) in id_plane.iter().enumerate() {
                        for (x, &id_val) in id_line.iter().enumerate() {
                            if id_val <= 0 {
                                continue;
                            }
                            if let Some(range) = ranges.get_mut(&id_val) {
                                range.expand(z, y, x);
                            } else {
                                ranges.insert(id_val, OccuRange::new(d, z, y, x));
                            }
                        }
                    }
                }
                let occus = ranges
                    .into_iter()
                    .map(|(id_val, range)| Occupancy::new(id_box, id_val, range))
                    .collect::<Vec<Occupancy>>();
                ret.push(occus);
            }
            ret
        }

        pub fn modify(
            &self,
            assigns: &[Vec<(usize, usize, usize)>],
            rand: &mut XorShift64,
        ) -> Self {
            let d = self.id_field[0].len();
            let mut ret = self.clone();
            let mut id_cnt = *self
                .id_field
                .iter()
                .map(|id_box| {
                    id_box
                        .iter()
                        .map(|id_plane| {
                            id_plane
                                .iter()
                                .map(|id_line| id_line.iter().max().unwrap())
                                .max()
                                .unwrap()
                        })
                        .max()
                        .unwrap()
                })
                .max()
                .unwrap();
            for (id_box, assign) in ret.id_field.iter_mut().zip(assigns.iter()) {
                let mut id_pair = BTreeMap::new();
                for &(z, y, x) in assign {
                    let id0 = id_box[z][y][x];
                    debug_assert!(id0 != 0);
                    for &(dz, dy, dx) in DELTAS.iter() {
                        if let Some(nz) = z.move_delta(dz, 0, d - 1) {
                            if let Some(ny) = y.move_delta(dy, 0, d - 1) {
                                if let Some(nx) = x.move_delta(dx, 0, d - 1) {
                                    let id1 = id_box[nz][ny][nx];
                                    if id1 == 0 {
                                        continue;
                                    }
                                    id_pair.entry(id0).or_insert(BTreeSet::new()).insert(id1);
                                }
                            }
                        }
                    }
                }
                let id_pair = id_pair
                    .into_iter()
                    .map(|(id0, id1s)| id1s.into_iter().map(|id1| (id0, id1)).collect::<Vec<_>>())
                    .collect::<Vec<_>>();
                for _ in 0..(if d <= 6 { 2 } else { 1 }) {
                    let i0 = rand.next_usize() % id_pair.len();
                    let i1 = rand.next_usize() % id_pair[i0].len();
                    let (id0, id1) = id_pair[i0][i1];
                    for &rem_id in [id0, id1].iter() {
                        for &(z, y, x) in assign.iter() {
                            if rem_id == id_box[z][y][x] {
                                id_cnt += 1;
                                id_box[z][y][x] = id_cnt;
                            } else if id_box[z][y][x] < 0 {
                                //id_cnt += 1;
                                //id_box[z][y][x] = id_cnt;
                            }
                        }
                    }
                }
            }
            for _ in 0..2 {
                ret.id_field = Self::bfs_connect(ret.id_field, assigns, rand);
            }
            ret
        }

        fn is_isolated(id_box: &[Vec<Vec<i32>>], pt: (usize, usize, usize)) -> bool {
            let d = id_box.len();
            let (z, y, x) = pt;
            for &(dz, dy, dx) in DELTAS.iter() {
                if let Some(nz) = z.move_delta(dz, 0, d - 1) {
                    if let Some(ny) = y.move_delta(dy, 0, d - 1) {
                        if let Some(nx) = x.move_delta(dx, 0, d - 1) {
                            let nid = id_box[nz][ny][nx];
                            if nid == 0 {
                                continue;
                            }
                            if nid == id_box[z][y][x] {
                                return false;
                            }
                        }
                    }
                }
            }
            true
        }

        fn can_move_to_isolated(id_box: &[Vec<Vec<i32>>], pt: (usize, usize, usize)) -> bool {
            debug_assert!(Self::is_isolated(id_box, pt));
            let d = id_box.len();
            let (z, y, x) = pt;
            for &(dz, dy, dx) in DELTAS.iter() {
                if let Some(nz) = z.move_delta(dz, 0, d - 1) {
                    if let Some(ny) = y.move_delta(dy, 0, d - 1) {
                        if let Some(nx) = x.move_delta(dx, 0, d - 1) {
                            let nid = id_box[nz][ny][nx];
                            if nid == 0 {
                                continue;
                            }
                            if Self::is_isolated(id_box, (nz, ny, nx)) {
                                return true;
                            }
                        }
                    }
                }
            }
            false
        }
        fn bfs_search(
            ini_pt: ((usize, usize, usize), (usize, usize, usize)),
            id_field: &[Vec<Vec<Vec<i32>>>],
            rot01: &RotDir3d,
        ) -> BfsResult {
            let d = id_field[0].len();
            let mut ret = BfsResult::new(d);
            let mut que = VecDeque::new();
            let ((z0, y0, x0), (z1, y1, x1)) = ini_pt;
            que.push_back((z0, y0, x0, vec![z1, y1, x1]));
            ret.dist01[z0][y0][x0] = Some((z1, y1, x1));
            ret.dist_count += 1;
            while let Some((z0, y0, x0, pt1)) = que.pop_front() {
                for &(dz0, dy0, dx0) in DELTAS.iter() {
                    //rand.next_permutation(6).into_iter().map(|i| DELTAS[i]) {
                    let delta_zto = if rot01.dirs[0].sign { dz0 } else { -dz0 };
                    let delta_yto = if rot01.dirs[1].sign { dy0 } else { -dy0 };
                    let delta_xto = if rot01.dirs[2].sign { dx0 } else { -dx0 };
                    if let Some(nz0) = z0.move_delta(dz0, 0, d - 1) {
                        if let Some(nzto) = pt1[rot01.dirs[0].to].move_delta(delta_zto, 0, d - 1) {
                            if let Some(ny0) = y0.move_delta(dy0, 0, d - 1) {
                                if let Some(nyto) =
                                    pt1[rot01.dirs[1].to].move_delta(delta_yto, 0, d - 1)
                                {
                                    if let Some(nx0) = x0.move_delta(dx0, 0, d - 1) {
                                        if let Some(nxto) =
                                            pt1[rot01.dirs[2].to].move_delta(delta_xto, 0, d - 1)
                                        {
                                            let nid0 = id_field[0][nz0][ny0][nx0];
                                            if nid0 == 0 {
                                                continue;
                                            }
                                            if ret.dist01[nz0][ny0][nx0].is_some() {
                                                continue;
                                            }
                                            if !Self::is_isolated(&id_field[0], (nz0, ny0, nx0)) {
                                                continue;
                                            }
                                            let mut npt1 = vec![0; 3];
                                            npt1[rot01.dirs[0].to] = nzto;
                                            npt1[rot01.dirs[1].to] = nyto;
                                            npt1[rot01.dirs[2].to] = nxto;
                                            let nid1 = id_field[1][npt1[0]][npt1[1]][npt1[2]];
                                            if nid1 == 0 {
                                                continue;
                                            }
                                            if !Self::is_isolated(
                                                &id_field[1],
                                                (npt1[0], npt1[1], npt1[2]),
                                            ) {
                                                continue;
                                            }
                                            ret.dist01[nz0][ny0][nx0] =
                                                Some((npt1[0], npt1[1], npt1[2]));
                                            ret.dist_count += 1;
                                            que.push_back((nz0, ny0, nx0, npt1));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            ret
        }
        fn bfs_connect(
            mut id_field: Vec<Vec<Vec<Vec<i32>>>>,
            assigns: &[Vec<(usize, usize, usize)>],
            rand: &mut XorShift64,
        ) -> Vec<Vec<Vec<Vec<i32>>>> {
            let d = id_field[0].len();
            let mut id_cnt = *id_field
                .iter()
                .map(|id_box| {
                    id_box
                        .iter()
                        .map(|id_plane| {
                            id_plane
                                .iter()
                                .map(|id_line| id_line.iter().max().unwrap())
                                .max()
                                .unwrap()
                        })
                        .max()
                        .unwrap()
                })
                .max()
                .unwrap();

            let mut best_res = BfsResult::new(d);
            'bfs_loop: for (z0, y0, x0) in rand
                .next_permutation(assigns[0].len())
                .into_iter()
                .map(|i| assigns[0][i])
            {
                if !Self::is_isolated(&id_field[0], (z0, y0, x0)) {
                    continue;
                }
                for (z1, y1, x1) in rand
                    .next_permutation(assigns[1].len())
                    .into_iter()
                    .map(|i| assigns[1][i])
                {
                    if !Self::is_isolated(&id_field[1], (z1, y1, x1)) {
                        continue;
                    }
                    for rot01 in RotDir3d::new().into_iter() {
                        let res = Self::bfs_search(((z0, y0, x0), (z1, y1, x1)), &id_field, &rot01);
                        if best_res.dist_count.chmax(res.dist_count) {
                            best_res.dist01 = res.dist01;
                        }
                    }
                    break 'bfs_loop;
                }
            }
            if best_res.dist_count > 0 {
                id_cnt += 1;
                let id_val0 = id_cnt;
                id_cnt += 1;
                let id_val1 = id_cnt;
                for &(z0, y0, x0) in assigns[0].iter() {
                    if let Some((z1, y1, x1)) = best_res.dist01[z0][y0][x0] {
                        id_field[0][z0][y0][x0] = id_val0;
                        id_field[1][z1][y1][x1] = id_val1;
                    }
                }
            }
            id_field
        }
    }
}
mod solver {
    static mut EVAL: bool = false;
    use crate::occupancy::Occupancy;
    use crate::state::*;
    use crate::xor_shift_64::XorShift64;
    use crate::ChangeMinMax;
    use crate::Flow;
    use std::collections::{BTreeMap, BTreeSet};
    use std::time::Instant;
    pub struct Solver {
        d: usize,
        silhouettes: Vec<Silhouette>,
        assigns: Vec<Vec<(usize, usize, usize)>>,
        start_time: Instant,
    }
    impl Solver {
        pub fn new() -> Self {
            use crate::procon_reader::*;
            let start_time = Instant::now();
            let mut args = std::env::args().collect::<Vec<String>>();
            args.remove(0);
            for arg in args {
                if arg == "eval" {
                    unsafe {
                        EVAL = true;
                    }
                }
            }
            let d = read::<usize>();
            let silhouettes = (0..2).map(|_| Silhouette::new(d)).collect::<Vec<_>>();
            let mut assigns = vec![vec![]; 2];
            for (assign, silhouette) in assigns.iter_mut().zip(silhouettes.iter()) {
                for z in 0..d {
                    for y in (0..d).filter(|&y| silhouette.zy[z][y]) {
                        for x in (0..d).filter(|&x| silhouette.zx[z][x]) {
                            assign.push((z, y, x));
                        }
                    }
                }
            }
            Self {
                d,
                silhouettes,
                assigns,
                start_time,
            }
        }
        #[allow(clippy::type_complexity)]
        fn max_match(
            state: &mut State,
            occs: &mut [Vec<Occupancy>],
        ) -> Vec<BTreeMap<usize, usize>> {
            let n0 = occs[0].len();
            let n1 = occs[1].len();

            let mut id_val = 0;
            for (id_box, occs) in state.id_field.iter_mut().zip(occs.iter()) {
                for occ in occs.iter() {
                    id_val += 1;
                    occ.write_id(id_box, id_val);
                }
            }

            let mut minf = Flow::new(n0 + n1 + 2);
            let mut maxf = Flow::new(n0 + n1 + 2);
            let src = n0 + n1;
            let dst = src + 1;
            for i0 in 0..n0 {
                for i1 in 0..n1 {
                    if occs[0][i0] != occs[1][i1] {
                        continue;
                    }
                    let cost0 = {
                        let occ = &mut occs[0][i0];
                        let (z, y, x) = occ.points()[0];
                        let id = state.id_field[0][z][y][x];
                        debug_assert!(id > 0);
                        occ.get_cost(&state.id_field[0], id)
                    };
                    let cost1 = {
                        let occ = &mut occs[1][i1];
                        let (z, y, x) = occ.points()[0];
                        let id = state.id_field[1][z][y][x];
                        debug_assert!(id > 0);
                        occ.get_cost(&state.id_field[1], id)
                    };
                    minf.add_cost_edge(i0, n0 + i1, 1, (cost0 + cost1).into());
                    maxf.add_edge(i0, n0 + i1, 1);
                }
            }
            for i0 in 0..occs[0].len() {
                minf.add_cost_edge(src, i0, 1, 0);
                maxf.add_edge(src, i0, 1);
            }
            for i1 in 0..occs[1].len() {
                minf.add_cost_edge(n0 + i1, dst, 1, 0);
                maxf.add_edge(n0 + i1, dst, 1);
            }
            let _ = minf.min_cost_flow(src, dst, maxf.max_flow(src, dst));

            let mut st = vec![BTreeMap::new(); 2];

            for (i0, _o0) in occs[0].iter().enumerate() {
                let id0_val = i0 as i32 + 1;
                for e in minf.g[i0].iter() {
                    if e.flow == 0 {
                        continue;
                    }
                    let i1 = e.to;
                    if !((n0 <= i1) && (i1 < n0 + n1)) {
                        continue;
                    }
                    let i1 = i1 - n0;
                    st[0].insert(i0, i1);
                    st[1].insert(i1, i0);
                    let o1 = &occs[1][i1];
                    o1.write_id(&mut state.id_field[1], id0_val);
                }
            }
            st
        }
        fn zx_any(id_box: &[Vec<Vec<i32>>], sz: usize, sx: usize, id_val: i32) -> bool {
            let d = id_box.len();
            for ay in 0..d {
                let aid = id_box[sz][ay][sx];
                if aid <= 0 {
                    continue;
                }
                if aid == id_val {
                    continue;
                }
                return true;
            }
            false
        }
        fn zy_any(id_box: &[Vec<Vec<i32>>], sz: usize, sy: usize, id_val: i32) -> bool {
            let d = id_box.len();
            for ax in 0..d {
                let aid = id_box[sz][sy][ax];
                if aid <= 0 {
                    continue;
                }
                if aid == id_val {
                    continue;
                }
                return true;
            }
            false
        }
        fn remove_useless(
            &self,
            id_field: &mut [Vec<Vec<Vec<i32>>>],
            mut occs: Vec<Vec<Occupancy>>,
            matches: Vec<BTreeMap<usize, usize>>,
        ) {
            let mut id_cnt = *id_field
                .iter()
                .map(|id_box| {
                    id_box
                        .iter()
                        .map(|id_plane| {
                            id_plane
                                .iter()
                                .map(|id_line| id_line.iter().max().unwrap())
                                .max()
                                .unwrap()
                        })
                        .max()
                        .unwrap()
                })
                .max()
                .unwrap();
            let mut id_cnt_min = std::cmp::min(
                -1,
                *id_field
                    .iter()
                    .map(|id_box| {
                        id_box
                            .iter()
                            .map(|id_plane| {
                                id_plane
                                    .iter()
                                    .map(|id_line| id_line.iter().max().unwrap())
                                    .min()
                                    .unwrap()
                            })
                            .min()
                            .unwrap()
                    })
                    .min()
                    .unwrap(),
            );
            // delete isolated box, if possible.
            for ((id_box, occs), (matches, silhouette)) in id_field
                .iter_mut()
                .zip(occs.iter_mut())
                .zip(matches.iter().zip(self.silhouettes.iter()))
            {
                let mut unmatches = vec![];
                let mut unmatches_order = vec![];
                for (oi, occ) in occs.iter().enumerate() {
                    if matches.contains_key(&oi) {
                        continue;
                    }
                    for (z, y, x) in occ.points() {
                        id_cnt += 1;
                        id_box[z][y][x] = id_cnt;
                    }
                    for occ in occ.to_units() {
                        unmatches.push(occ);
                        unmatches_order.push(unmatches_order.len());
                    }
                }
                unmatches_order.sort_by_cached_key(|&i| {
                    let occ = &mut unmatches[i];
                    debug_assert!(occ.eff_size() == 1);
                    let (z, y, x) = occ.points()[0];
                    let id_val = id_box[z][y][x];
                    let val: i64 = occ.get_cost(id_box, id_val).into();
                    val
                });
                for ui in unmatches_order {
                    let occ = &unmatches[ui];
                    if Self::can_delete(silhouette, id_box, occ) {
                        id_cnt_min -= 1;
                        occ.write_id(id_box, id_cnt_min);
                    }
                }
            }

            let mut match_pairs = vec![];
            for (&oi0, &oi1) in matches[0].iter() {
                match_pairs.push((oi0, oi1));
            }
            match_pairs.sort_by_cached_key(|&(oi0, oi1)| -> i64 {
                let cost0 = {
                    let occ = &mut occs[0][oi0];
                    let (z, y, x) = occ.points()[0];
                    occ.get_cost(&id_field[0], id_field[0][z][y][x])
                };
                let cost1 = {
                    let occ = &mut occs[1][oi1];
                    let (z, y, x) = occ.points()[0];
                    occ.get_cost(&id_field[1], id_field[1][z][y][x])
                };
                (cost0 + cost1).into()
            });
            for (oi0, oi1) in match_pairs {
                debug_assert!(matches[0].contains_key(&oi0));
                debug_assert!(matches[1].contains_key(&oi1));
                if !Self::can_delete(&self.silhouettes[0], &id_field[0], &occs[0][oi0]) {
                    continue;
                }
                if !Self::can_delete(&self.silhouettes[1], &id_field[1], &occs[1][oi1]) {
                    continue;
                }
                id_cnt_min -= 1;
                occs[0][oi0].write_id(&mut id_field[0], id_cnt_min);
                id_cnt_min -= 1;
                occs[1][oi1].write_id(&mut id_field[1], id_cnt_min);
            }
        }
        fn can_delete(silhouette: &Silhouette, id_box: &[Vec<Vec<i32>>], occ: &Occupancy) -> bool {
            for (z, y, x) in occ.points() {
                let occ_id = id_box[z][y][x];
                if silhouette.zy[z][y] && silhouette.zx[z][x] {
                    // occupates, and needed.
                    if !Self::zy_any(id_box, z, y, occ_id) {
                        return false;
                    }
                    if !Self::zx_any(id_box, z, x, occ_id) {
                        return false;
                    }
                }
            }
            true
        }
        fn output(&self, state: State) {
            let id_field = state.id_field;
            if unsafe { !EVAL } {
                let mut st = std::collections::HashMap::new();
                for bx in id_field.iter() {
                    for plane in bx.iter() {
                        for line in plane.iter() {
                            for &val in line.iter().filter(|&&val| val > 0) {
                                st.insert(val, 0);
                            }
                        }
                    }
                }
                for (i, (_, v)) in st.iter_mut().enumerate() {
                    *v = i + 1;
                }
                println!("{}", st.len());
                for id_box in &id_field {
                    for x in 0..self.d {
                        for y in 0..self.d {
                            for plane in id_box.iter() {
                                let val = plane[y][x];
                                if val <= 0 {
                                    print!("0 ");
                                } else {
                                    print!("{} ", st[&val]);
                                }
                            }
                        }
                    }
                    println!();
                }
            } else {
                println!("{}", self.evaluate(&id_field));
            }
        }
        fn evaluate(&self, id_field: &[Vec<Vec<Vec<i32>>>]) -> usize {
            if cfg!(debug_assertions) {
                let mut cnt_2d = vec![vec![vec![vec![0; self.d]; self.d]; self.d]; 2];
                for (id_box, cnt) in id_field.iter().zip(cnt_2d.iter_mut()) {
                    for (id_plane, cnt) in id_box.iter().zip(cnt.iter_mut()) {
                        for (id_line, cnt) in id_plane.iter().zip(cnt.iter_mut()) {
                            for (&id_val, cnt) in id_line.iter().zip(cnt.iter_mut()) {
                                if id_val > 0 {
                                    *cnt += 1;
                                }
                            }
                        }
                    }
                }
                for (silhouette, cnt) in self.silhouettes.iter().zip(cnt_2d.iter()) {
                    for (z, cnt) in cnt.iter().enumerate() {
                        for (y, cnt) in cnt.iter().enumerate() {
                            let sm = cnt.iter().sum::<usize>();
                            if silhouette.zy[z][y] {
                                debug_assert!(sm > 0);
                            } else {
                                debug_assert!(sm == 0);
                            }
                        }
                        for x in 0..self.d {
                            let sm = (0..self.d).map(|y| cnt[y][x]).sum::<usize>();
                            if silhouette.zx[z][x] {
                                debug_assert!(sm > 0);
                            } else {
                                debug_assert!(sm == 0);
                            }
                        }
                    }
                }
            }

            let mut cnt = vec![BTreeMap::new(); 2];
            for (cnt, id_box) in cnt.iter_mut().zip(id_field.iter()) {
                for id_plane in id_box {
                    for id_line in id_plane {
                        for &id_val in id_line.iter().filter(|&&id_val| id_val > 0) {
                            *cnt.entry(id_val).or_insert(0) += 1;
                        }
                    }
                }
            }
            let mut scores = vec![0.0; 2];
            let mut isos = vec![BTreeSet::new(); 2];
            for si in 0..2 {
                for (&id_val, &v) in cnt[si].iter() {
                    if !cnt[1 - si].contains_key(&id_val) {
                        scores[si] += v as f64;
                        isos[si].insert(id_val);
                    }
                }
            }
            let mut score = scores.into_iter().sum::<f64>();
            for (cnt, iso) in cnt.iter_mut().zip(isos.iter()) {
                for iso in iso.iter() {
                    cnt.remove(iso);
                }
            }
            for (_, &v) in cnt[0].iter() {
                score += 1.0 / v as f64;
            }
            f64::round(score * 1e9) as usize
        }
        fn debug_id_field(&self, id_field: &[Vec<Vec<Vec<i32>>>]) {
            if !cfg!(debug_assertions) {
                return;
            }
            for (silhouette, id_box) in self.silhouettes.iter().zip(id_field.iter()) {
                let mut zy_cnt = vec![vec![0; self.d]; self.d];
                let mut zx_cnt = vec![vec![0; self.d]; self.d];
                for (z, id_plane) in id_box.iter().enumerate() {
                    for (y, id_line) in id_plane.iter().enumerate() {
                        for (x, &id_val) in id_line.iter().enumerate() {
                            if id_val > 0 {
                                zy_cnt[z][y] += 1;
                                zx_cnt[z][x] += 1;
                                debug_assert!(silhouette.zy[z][y]);
                                debug_assert!(silhouette.zx[z][x]);
                            }
                        }
                    }
                }
                for (sil_plane, cnt_plane) in silhouette.zy.iter().zip(zy_cnt.iter()) {
                    for (&sil, &cnt) in sil_plane.iter().zip(cnt_plane.iter()) {
                        if sil {
                            debug_assert!(cnt > 0);
                        } else {
                            debug_assert!(cnt == 0);
                        }
                    }
                }
                for (sil_plane, cnt_plane) in silhouette.zx.iter().zip(zx_cnt.iter()) {
                    for (&sil, &cnt) in sil_plane.iter().zip(cnt_plane.iter()) {
                        if sil {
                            debug_assert!(cnt > 0);
                        } else {
                            debug_assert!(cnt == 0);
                        }
                    }
                }
            }
        }
        fn debug_occupancies(&self, occs: &[Vec<Occupancy>]) {
            if !cfg!(debug_assertions) {
                return;
            }
            for (silhouette, occs) in self.silhouettes.iter().zip(occs.iter()) {
                let mut zy_cnt = vec![vec![0; self.d]; self.d];
                let mut zx_cnt = vec![vec![0; self.d]; self.d];
                for occ in occs {
                    for z in occ.get_range().zrange() {
                        for y in occ.get_range().yrange() {
                            for x in occ.get_range().xrange() {
                                if occ.get(z, y, x) {
                                    debug_assert!(silhouette.zy[z][y]);
                                    debug_assert!(silhouette.zx[z][x]);
                                    zy_cnt[z][y] += 1;
                                    zx_cnt[z][x] += 1;
                                }
                            }
                        }
                    }
                }
                for z in 0..self.d {
                    for y in 0..self.d {
                        if silhouette.zy[z][y] {
                            assert!(zy_cnt[z][y] > 0);
                        } else {
                            assert!(zy_cnt[z][y] == 0);
                        }
                    }
                    for x in 0..self.d {
                        if silhouette.zx[z][x] {
                            assert!(zx_cnt[z][x] > 0);
                        } else {
                            assert!(zx_cnt[z][x] == 0);
                        }
                    }
                }
            }
        }
        fn refine(&self, state: &mut State) {
            while State::refine(state) {}
            //ret.connect_isolated_blocks();
            self.debug_id_field(&state.id_field);
            let mut occs = state.positive_occupancies();
            self.debug_occupancies(&occs);
            let matches = Self::max_match(state, &mut occs);
            self.debug_id_field(&state.id_field);
            self.remove_useless(&mut state.id_field, occs, matches);
        }
        pub fn solve(&mut self) {
            let mut rand = XorShift64::new();
            let mut pivot_state = State::new(&self.silhouettes, self.d);
            let mut best_state = pivot_state.clone();
            let mut best_score = self.evaluate(&best_state.id_field);
            let mut lc = 0;
            let max_milli = 5_000;
            let prob_th0 = 0.01;
            let mut prob_th = prob_th0;
            let mut elapsed = self.start_time.elapsed().as_millis() as u64;
            while elapsed < max_milli {
                lc += 1;
                if lc % 10 == 0 {
                    let proc = elapsed as f64 / max_milli as f64;
                    prob_th = prob_th0 * (-proc).exp();
                }
                let mut next_state = pivot_state.modify(&self.assigns, &mut rand);
                self.refine(&mut next_state);
                let next_score = self.evaluate(&next_state.id_field);
                if best_score.chmin(next_score) {
                    //eprintln!("{}", lc);
                    best_state = next_state.clone();
                    pivot_state = next_state.clone();
                } else if rand.next_f64() < prob_th {
                    //    pivot_state = next_state.clone();
                }
                elapsed = self.start_time.elapsed().as_millis() as u64;
            }
            //eprintln!("{}", lc);
            self.output(best_state);
        }
    }
}

fn main() {
    solver::Solver::new().solve();
}
