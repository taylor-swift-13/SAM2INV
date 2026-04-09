int main1(int k){
  int bld, tx, a;
  bld=k;
  tx=0;
  a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre) + tx * bld;
  loop invariant bld == \at(k, Pre);
  loop invariant tx >= 0;
  loop invariant 0 <= a;
  loop invariant a <= 2 * tx;
  loop invariant (a % 2) == 0;
  loop invariant (bld >= 0) ==> (tx <= bld);
  loop invariant (tx <= bld/2) ==> (a == 0);
  loop assigns a, tx, k;
*/
while (tx<bld) {
      if (!(!(tx>=bld/2))) {
          a += 2;
      }
      tx += 1;
      k += bld;
  }
}