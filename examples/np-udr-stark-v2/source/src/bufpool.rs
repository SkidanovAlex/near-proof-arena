//! A small pool of large `Vec<F>` buffers.
//!
//! Large allocations are fresh `mmap`s under glibc (and `prover::malloc_tune`
//! pins the threshold at 1 MB): every 512 MB block buffer used to be
//! page-faulted and zeroed by the kernel again, 4 KiB at a time. Hot loops
//! take their buffers here and give them back when done.
//!
//! [`take`] returns a buffer of the requested length whose contents are
//! stale (but initialized) field elements: callers must overwrite all of it.
//! The pool holds at most [`LIMIT`] bytes; [`clear`] releases everything (at
//! phase ends, so that pooled buffers do not add to the peak of the next
//! phase).

use std::sync::Mutex;

use p3_field::PrimeCharacteristicRing;

use crate::field::F;

/// Buffers smaller than this are not pooled.
const MIN: usize = 1 << 18;
/// Bytes held by the pool at most.
pub const LIMIT: usize = 3 << 29;

static POOL: Mutex<Vec<Vec<F>>> = Mutex::new(Vec::new());

/// A buffer of `n` elements with arbitrary (stale) contents.
pub fn take(n: usize) -> Vec<F> {
    if n >= MIN {
        let mut p = POOL.lock().unwrap();
        // best fit: the smallest buffer that holds `n`
        let best = p
            .iter()
            .enumerate()
            .filter(|(_, v)| v.len() >= n)
            .min_by_key(|(_, v)| v.len())
            .map(|(i, _)| i);
        if let Some(i) = best {
            let mut v = p.swap_remove(i);
            drop(p);
            v.truncate(n);
            return v;
        }
    }
    vec![F::ZERO; n]
}

/// Return a buffer to the pool (dropped if small or if the pool is full).
pub fn give(mut v: Vec<F>) {
    if v.len() < MIN {
        return;
    }
    // only the initialized length is reused
    v.shrink_to(v.len());
    if v.capacity() != v.len() {
        return;
    }
    let bytes = v.len() * 4;
    let mut p = POOL.lock().unwrap();
    let mut held: usize = p.iter().map(|x| x.len() * 4).sum();
    while held + bytes > LIMIT && !p.is_empty() {
        // evict the smallest
        let i = (0..p.len()).min_by_key(|&i| p[i].len()).unwrap();
        held -= p[i].len() * 4;
        p.swap_remove(i);
    }
    if held + bytes <= LIMIT {
        p.push(v);
    }
}

/// Release every pooled buffer.
pub fn clear() {
    let v = std::mem::take(&mut *POOL.lock().unwrap());
    drop(v);
}
