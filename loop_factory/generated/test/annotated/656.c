int main1(int l,int s){
  int ys, wq0, pq, ii, ff;
  ys=75;
  wq0=0;
  pq=1;
  ii=0;
  ff=wq0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ii == (pq - 1)*(pq - 1);
  loop invariant l == \at(l, Pre) + (pq - 1) * ys;
  loop invariant 1 <= pq <= ys + 1;
  loop assigns ii, l, pq;
*/
while (1) {
      if (!(pq<=ys)) {
          break;
      }
      ii = ii+2*pq-1;
      l += ys;
      pq = pq + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ff == 0;
  loop assigns ii;
*/
while (ii+3<=ff) {
      ii = ii + 3;
  }
}