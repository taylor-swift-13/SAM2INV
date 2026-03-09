int main1(int k,int n){
  int y, hk, d1mr, my1;
  y=(k%6)+7;
  hk=0;
  d1mr=1;
  my1=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (d1mr == my1);
  loop invariant (hk % 4 == 0);
  loop invariant (k - \at(k,Pre)) == hk + (hk * hk) / 8;
  loop invariant my1 == hk + 1;
  loop invariant y == (\at(k, Pre) % 6) + 7;
  loop invariant 0 <= hk;
  loop invariant hk <= y + 3;
  loop assigns d1mr, my1, hk, k;
*/
while (1) {
      if (!(hk<y)) {
          break;
      }
      d1mr += 4;
      my1 += 4;
      hk += 4;
      k = k + hk;
      k += 2;
  }
}