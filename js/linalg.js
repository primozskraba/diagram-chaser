// Sparse vectors (Map key -> Q) and an echelon basis that tracks, for every
// row, a "tag": a sparse record of how the row was built from named inputs.
import { Q, ONE } from './rational.js';

export function vec(entries = []) {
  const v = new Map();
  for (const [k, c] of entries) addTo(v, k, Q.of(c));
  return v;
}

export function addTo(v, k, c) {
  if (c.isZero()) return v;
  const cur = v.get(k);
  const nxt = cur ? cur.add(c) : c;
  if (nxt.isZero()) v.delete(k); else v.set(k, nxt);
  return v;
}

/** returns a + c * b (new map) */
export function axpy(a, c, b) {
  const out = new Map(a);
  if (c.isZero()) return out;
  for (const [k, x] of b) addTo(out, k, x.mul(c));
  return out;
}

export function scale(a, c) {
  const out = new Map();
  if (c.isZero()) return out;
  for (const [k, x] of a) out.set(k, x.mul(c));
  return out;
}

export function isZeroVec(v) { return v.size === 0; }

export class TrackedBasis {
  /** order: key -> number (pivot = key of largest order) */
  constructor(order) {
    this.order = order;
    this.rows = new Map(); // pivotKey -> {vec, tag}
  }
  clone() {
    const b = new TrackedBasis(this.order);
    for (const [k, r] of this.rows) b.rows.set(k, r);
    return b;
  }
  pivotOf(v) {
    let best = null, bo = -Infinity;
    for (const k of v.keys()) {
      const o = this.order(k);
      if (o > bo) { bo = o; best = k; }
    }
    return best;
  }
  /** reduce (v, tag) by the rows; returns residual and updated tag with
   *  invariant: v_in - v_out = sum c_i row_i  and  tag_in - tag_out = sum c_i tag_i */
  reduce(v, tag = new Map()) {
    v = new Map(v); tag = new Map(tag);
    for (;;) {
      // find the largest-order key of v that is a pivot
      let best = null, bo = -Infinity;
      for (const k of v.keys()) {
        if (!this.rows.has(k)) continue;
        const o = this.order(k);
        if (o > bo) { bo = o; best = k; }
      }
      if (best === null) return { vec: v, tag };
      const row = this.rows.get(best);
      const c = v.get(best).div(row.vec.get(best)).neg();
      v = axpy(v, c, row.vec);
      tag = axpy(tag, c, row.tag);
    }
  }
  /** insert; returns the reduced residual/tag. If residual is zero nothing is added. */
  insert(v, tag = new Map()) {
    const r = this.reduce(v, tag);
    if (r.vec.size) {
      // make every key of the new row respect echelon form: pivot = max key
      const p = this.pivotOf(r.vec);
      if (this.rows.has(p)) throw new Error('pivot clash');
      this.rows.set(p, r);
    }
    return r;
  }
  /** Express v as a combination: returns tag S with v = sum S (w.r.t. row tags), or null. */
  express(v) {
    const r = this.reduce(v, new Map());
    if (r.vec.size) return null;
    // v - sum c_i row_i = 0 and 0 - tag_out = sum c_i tag_i  =>  v = -tag_out
    return scale(r.tag, ONE.neg());
  }
}
