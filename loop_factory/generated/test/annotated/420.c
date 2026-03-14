int main1(){
  int gx, oa, t, nnm, h5, g;
  gx=158;
  oa=gx;
  t=0;
  nnm=0;
  h5=0;
  g=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= nnm;
  loop invariant nnm < 5;
  loop invariant 0 <= h5;
  loop invariant h5 < 5;
  loop invariant 158 <= oa;
  loop invariant oa <= gx;
  loop invariant -4*(oa - 158) <= t;
  loop invariant t <= 4*(oa - 158);
  loop assigns nnm, h5, t, oa, g;
*/
while (oa<=gx-1) {
      nnm = oa%5;
      if (oa>=g) {
          h5 = (oa-g)%5;
          t = t+nnm-h5;
      }
      else {
          t = t + nnm;
      }
      oa++;
      g += t;
  }
}