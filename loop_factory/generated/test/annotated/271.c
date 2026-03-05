int main1(int k){
  int bz, nj, npah;
  bz=63;
  nj=bz;
  npah=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bz == 63;
  loop invariant nj == 63;
  loop invariant npah >= -1;
  loop invariant k == \at(k, Pre) + 64 * (npah + 1);
  loop assigns k, npah;
*/
while (nj>0) {
      if (nj<bz/2) {
          npah = npah + npah;
      }
      else {
          npah = npah + 1;
      }
      k = k+(nj%2);
      k = bz+k;
  }
}