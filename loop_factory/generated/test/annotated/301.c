int main1(int z){
  int d6p2, v5, nw, i6, qv;
  d6p2=z*2;
  v5=0;
  nw=0;
  i6=z;
  qv=d6p2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qv == d6p2 + nw*(nw+1)/2;
  loop invariant d6p2 == 2 * z;
  loop invariant (nw == 0) ==> (i6 == z);
  loop invariant (nw > 0) ==> (i6 == d6p2 - (nw - 1));
  loop invariant nw >= 0;
  loop assigns i6, nw, qv;
*/
while (1) {
      if (!(nw<d6p2)) {
          break;
      }
      i6 = (d6p2)+(-(nw));
      nw++;
      qv = qv + nw;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v5 >= 0;
  loop invariant ((i6 <= 0) ==> (v5 == 0));
  loop assigns v5;
*/
while (1) {
      if (!(v5+1<=i6)) {
          break;
      }
      v5 = v5 + 1;
  }
}