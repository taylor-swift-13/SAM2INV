int main1(){
  int l, m, ws5, blh, f;
  l=1;
  m=l;
  ws5=0;
  blh=0;
  f=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ws5 == blh;
  loop invariant l == 1;
  loop invariant m == l;
  loop invariant f == blh + 3;
  loop assigns f, ws5, blh;
*/
while (blh<=l-1) {
      f = f + m;
      ws5 += 1;
      blh++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant blh <= f;
  loop assigns blh, l;
*/
while (blh<=f-1) {
      blh++;
      l = l + 1;
      if (l+5<f) {
          l += l;
      }
  }
}