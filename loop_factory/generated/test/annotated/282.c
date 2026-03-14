int main1(){
  int j52f, u3zx, q, gd, r4, aste;
  j52f=1+22;
  u3zx=0;
  q=0;
  gd=0;
  r4=0;
  aste=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aste == 4 + 10*(u3zx/5) + ((u3zx%5)*((u3zx%5) - 1))/2;
  loop invariant j52f == 1 + 22;
  loop invariant 0 <= u3zx <= j52f;
  loop invariant q <= aste;
  loop invariant 4 <= aste - q;
  loop invariant 0 <= q <= 4*j52f;
  loop invariant 4 <= aste <= 4 + 4*u3zx;
  loop invariant 0 <= gd <= 4;
  loop invariant 0 <= r4 <= 4;
  loop assigns gd, r4, q, aste, u3zx;
*/
while (u3zx<=j52f-1) {
      gd = u3zx%5;
      if (!(!(u3zx>=aste))) {
          r4 = (u3zx-aste)%5;
          q = q+gd-r4;
      }
      else {
          q = q + gd;
      }
      aste = aste + gd;
      u3zx += 1;
  }
}