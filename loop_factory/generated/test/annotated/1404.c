int main1(){
  int n7, n1v, dx, re, y9, i, m;
  n7=61;
  n1v=3;
  dx=n7;
  re=2;
  y9=n1v;
  i=-6;
  m=n7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y9 == 4*i + 27;
  loop invariant re == 2*i*i + 25*i + 80;
  loop invariant m >= 61;
  loop invariant dx >= 61;
  loop invariant y9 >= 3;
  loop invariant i <= (n7 + 1);
  loop invariant dx >= n7;
  loop invariant y9 > 0;
  loop assigns dx, re, m, i, y9;
*/
while (1) {
      if (i>n7) {
          break;
      }
      dx = dx + re;
      re += y9;
      m = m+(dx%3);
      i = i + 1;
      y9 += 4;
  }
}