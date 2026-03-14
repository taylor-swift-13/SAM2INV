int main1(int t){
  int gx, g, f4sd, v9, ndj;
  gx=56;
  g=gx;
  f4sd=38;
  v9=1;
  ndj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == gx + ndj;
  loop invariant v9 == 1 + ndj;
  loop invariant (ndj == 0) ==> (f4sd == 38);
  loop invariant (ndj >= 1) ==> (f4sd <= 0);
  loop invariant g == 56 + ndj;
  loop invariant 0 <= ndj <= 1;
  loop invariant 0 <= f4sd <= 38;
  loop assigns f4sd, g, ndj, v9;
*/
while (1) {
      if (!(f4sd>0&&v9<=gx)) {
          break;
      }
      if (!(f4sd<=v9)) {
          f4sd = 0;
      }
      else {
          f4sd = f4sd - v9;
      }
      g++;
      ndj++;
      v9++;
  }
}