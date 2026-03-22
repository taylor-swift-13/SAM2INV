int main1(int q){
  int s7e6, ypw, e1, fbz, g;
  s7e6=q+15;
  ypw=s7e6;
  e1=0;
  fbz=s7e6;
  g=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == \at(q, Pre);
  loop invariant s7e6 == \at(q, Pre) + 15;
  loop invariant ypw == s7e6;
  loop invariant e1 >= 0;
  loop invariant e1 % 10 == 0;
  loop assigns fbz, e1, q;
*/
while (e1<=s7e6-1) {
      fbz = e1;
      e1 = e1 + 10;
      q = q+s7e6-ypw;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s7e6 == \at(q, Pre) + 15;
  loop invariant ypw == s7e6;
  loop invariant e1 >= 0;
  loop invariant (ypw == 0) ==> (q == \at(q, Pre));
  loop assigns g, e1, q;
*/
while (e1<ypw) {
      g = g + q;
      e1 = e1 + 1;
      q += ypw;
  }
}