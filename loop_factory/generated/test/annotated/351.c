int main1(int q){
  int yc, p, d, ur;
  yc=0;
  p=0;
  d=0;
  ur=(q%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == p;
  loop invariant p == yc;
  loop invariant yc >= 0;
  loop assigns d, yc, ur, p, q;
*/
while (ur>0) {
      d = d+q*q;
      yc = yc+q*q;
      ur--;
      p = p+q*q;
      q += yc;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p >= 0;
  loop invariant d >= 0;
  loop invariant yc >= 0;
  loop assigns d, yc, q;
*/
while (d>yc) {
      d -= yc;
      yc = (1)+(yc);
      q += p;
  }
}