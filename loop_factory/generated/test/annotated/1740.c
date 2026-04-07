int main1(){
  int tb, czt, ji, si, x, m;
  tb=1*3;
  czt=0;
  ji=0;
  si=3;
  x=0;
  m=tb;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ji;
  loop invariant ji <= tb;
  loop invariant x == ji * m;
  loop invariant si == 3 + ji*(ji-1)/2;
  loop invariant x == ji * (czt + m);
  loop invariant m == tb;
  loop assigns si, x, ji;
*/
while (ji<=tb-1) {
      si = si + ji;
      x = x + czt;
      ji++;
      x = x + m;
  }
}