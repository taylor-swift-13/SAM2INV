int main1(int d){
  int k2, w5, x, jbqw, b6;
  k2=27;
  w5=2;
  x=1;
  jbqw=0;
  b6=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jbqw == (x-1)*(x-1);
  loop invariant b6 == 4 + w5*(x-1);
  loop invariant 1 <= x;
  loop invariant x <= k2 + 1;
  loop invariant k2   == 27;
  loop assigns jbqw, b6, x;
*/
while (1) {
      if (!(x<=k2)) {
          break;
      }
      jbqw = (jbqw+2*x)+(-(1));
      b6 += w5;
      x = x + 1;
  }
}