int main1(){
  int j6, ma, d8j, x, d, ww, i, mo, ir;
  j6=73;
  ma=0;
  d8j=6;
  x=j6;
  d=5;
  ww=0;
  i=0;
  mo=0;
  ir=-2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 3 * ma;
  loop invariant ir == 2 * ma - 2;
  loop invariant mo == 0;
  loop invariant ww == 5 * ma;
  loop invariant x == 73 + (5 * ma * (ma + 1)) / 2 + 2 * ma;
  loop invariant j6 == 73;
  loop invariant 0 <= ma;
  loop invariant ma <= j6;
  loop invariant d8j - ma == 6;
  loop invariant d == 5;
  loop assigns ma, d8j, ww, x, ir, i;
*/
while (ma < j6) {
      ma += 1;
      if (mo == 0) {
          d8j++;
      }
      if (!(mo!=1)) {
          mo = 1;
      }
      else {
          ww += d;
      }
      x += ww;
      ir += 2;
      x += 2;
      i = i + 3;
  }
}