int main1(int l){
  int ich, f5, dc, xzw;
  ich=l+16;
  f5=0;
  dc=11;
  xzw=-3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ich == \at(l, Pre) + 16;
  loop invariant dc == 11 + 2 * f5;
  loop invariant xzw == -3 + f5 * ich - (f5 * (f5 - 1)) / 2;
  loop invariant f5 >= 0;
  loop invariant (ich >= 0) ==> (f5 <= ich);
  loop assigns f5, dc, xzw;
*/
while (1) {
      if (f5>=ich) {
          break;
      }
      f5 += 1;
      dc += 2;
      xzw = xzw+ich-f5;
      xzw++;
  }
}