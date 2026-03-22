int main1(int m){
  int w, m394, ji, r;
  w=m*4;
  m394=-5;
  ji=w;
  r=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (w == 4*m) || (w == m394);
  loop invariant (r != 7) ==> (ji == r * r);
  loop invariant m == \at(m, Pre);
  loop invariant m394 == -5;
  loop invariant r >= 7;
  loop invariant (r == 7) ==> (ji == w);
  loop assigns r, ji, w;
*/
while (m394+1<=w) {
      r = r + 1;
      ji = r*r;
      w = (m394+1)-1;
  }
}