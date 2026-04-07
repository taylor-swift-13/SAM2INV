int main1(){
  int s, ma, d9, x, dm;
  s=1-10;
  ma=0;
  d9=0;
  x=0;
  dm=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == ma;
  loop invariant dm == d9 - x;
  loop invariant s == 1 - 10;
  loop invariant d9 == x * x;
  loop invariant ma >= 0;
  loop assigns ma, d9, x, dm;
*/
while (1) {
      if (!(ma < s)) {
          break;
      }
      ma += 1;
      d9 = ma * ma;
      x = ma;
      dm = d9 - x;
  }
}