int main1(int m){
  int rgv, bo, ks0, d8er;
  rgv=m;
  bo=0;
  ks0=0;
  d8er=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ks0 == (bo * bo));
  loop invariant (d8er == (1 + 2 * bo));
  loop invariant bo >= 0;
  loop invariant rgv == \at(m, Pre);
  loop invariant (rgv >= 0) ==> (bo <= rgv);
  loop assigns ks0, bo, d8er;
*/
while (bo<rgv) {
      ks0 = ks0 + d8er;
      bo += 1;
      d8er += 2;
  }
}