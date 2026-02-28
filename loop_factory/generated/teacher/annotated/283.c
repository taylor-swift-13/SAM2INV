int main1(int m,int p){
  int b, u, x, n;

  b=19;
  u=0;
  x=5;
  n=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x % 6 == 5;
  loop invariant x >= 5;
  loop invariant x <= b + 5;
  loop invariant n <= x;
  loop invariant n >= 0;
  loop invariant m == \at(m, Pre);
  loop invariant (x - 5) % 6 == 0;
  loop invariant n == 3 * ((x - 5) / 6) + 5 * (((x - 5) / 6) % 2);
  loop invariant b == 19;

  loop invariant p == \at(p, Pre);

  loop invariant n >= -3;
  loop assigns x, n;
*/
while (x<b) {
      if (x<b) {
          x = x+1;
      }
      x = x+5;
      n = n+2;
      if (p<p+5) {
          n = n+1;
      }
      n = x-n;
  }

}
