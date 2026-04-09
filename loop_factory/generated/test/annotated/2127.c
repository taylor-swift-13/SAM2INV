int main1(){
  int xja, xfe, i5q, d, vd;
  xja=(1%40)+17;
  xfe=xja;
  i5q=xja;
  d=xja;
  vd=xja;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (d - xja) == 6 * (vd - xja);
  loop invariant 0 <= (vd - xja);
  loop invariant (vd - xja) <= 1;
  loop invariant i5q == xja*(1 + (vd - xja)) + 3*(vd - xja)*((vd - xja) - 1);
  loop invariant xfe == xja*(1 + (((vd - xja)*((vd - xja) + 1))/2)) + (vd - xja)*((vd - xja) - 1)*((vd - xja) - 2);
  loop invariant (d == 6*vd - 90);
  loop assigns xfe, i5q, d, vd;
*/
while (1) {
      if (vd>xja) {
          break;
      }
      xfe = xfe + i5q;
      i5q += d;
      d += 6;
      vd = (1)+(vd);
  }
}