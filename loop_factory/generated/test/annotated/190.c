int main1(int k){
  int ci;
  ci=-10804;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ci <= -10804;
  loop invariant k - 2*ci >= \at(k, Pre) + 21608;
  loop invariant k - ci <= \at(k, Pre) + 10804;
  loop assigns ci, k;
*/
while (ci<=-6) {
      ci = ci+ci-2;
      ci = ci + 1;
      k += ci;
  }
}