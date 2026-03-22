int main1(){
  int sx, ycv5, tq, t;
  sx=1;
  ycv5=0;
  tq=sx;
  t=ycv5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ycv5;
  loop invariant ycv5 <= sx;
  loop invariant tq == 1 + ycv5*sx;
  loop invariant t == ycv5 + (sx * ycv5 * (ycv5 - 1)) / 2;
  loop invariant tq == 1 + ycv5;
  loop invariant t == ycv5 + ycv5*(ycv5 - 1)/2;
  loop assigns ycv5, t, tq;
*/
while (ycv5 < sx) {
      ycv5++;
      t = t + tq;
      tq = tq + sx;
  }
}