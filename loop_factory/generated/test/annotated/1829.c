int main1(){
  int y42, q9ao, j, r84f, a0x, do9;
  y42=10;
  q9ao=0;
  j=0;
  r84f=0;
  a0x=0;
  do9=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= q9ao <= y42;
  loop invariant 0 <= a0x <= q9ao;
  loop invariant r84f >= 0;
  loop invariant 0 <= do9;
  loop invariant do9 <= 1;
  loop invariant 0 <= a0x <= y42 - 1;
  loop invariant 0 <= j <= 1;
  loop invariant (q9ao < y42) ==> (do9 == 0);
  loop invariant (q9ao < y42) ==> (j == 0);
  loop invariant r84f <= q9ao * a0x;
  loop invariant ((q9ao <= y42 - 1) ==> (a0x == q9ao)) &&
                 ((q9ao >= y42) ==> (a0x == y42 - 1));
  loop invariant (r84f <= y42 * (y42 - 1));
  loop assigns q9ao, do9, a0x, j, r84f;
*/
while (q9ao < y42) {
      q9ao = q9ao + 1;
      do9 = ((q9ao >= y42))+(do9);
      a0x = a0x + (q9ao < y42);
      j = j + (q9ao == y42);
      r84f = r84f + a0x;
  }
}