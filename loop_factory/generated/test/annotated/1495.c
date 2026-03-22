int main1(int k){
  int h0, did, nv, pb, s;
  h0=66;
  did=h0;
  nv=did;
  pb=did;
  s=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 1;
  loop invariant k >= \at(k, Pre);
  loop invariant pb >= h0;
  loop invariant nv >= h0;
  loop invariant pb % h0 == 0;
  loop invariant nv <= h0 + 1;
  loop assigns pb, s, nv, k;
*/
while (nv<=h0) {
      pb = pb*nv;
      if (nv<h0) {
          s = s*nv;
      }
      nv = nv + 1;
      k += pb;
  }
}