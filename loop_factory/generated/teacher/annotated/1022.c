int main1(int m,int n){
  int c, u, g, v;

  c=n+13;
  u=0;
  g=-2;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(n, Pre) + 13;
  loop invariant m == \at(m, Pre);
  loop invariant u >= 0;
  loop invariant (g + 9) % 7 == 0;
  loop invariant g + 9 > 0;
  loop invariant g >= -9;
  loop invariant n == \at(n, Pre);

  loop invariant g - 2*u >= -2;

  loop invariant c == \at(n,Pre) + 13;
  loop invariant m == \at(m,Pre) && n == \at(n,Pre);
  loop invariant (g + 9) % 7 == 0 && u >= 0 && c == \at(n, Pre) + 13;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant (u == 0 || u <= c);
  loop invariant g >= 7*u - 2;
  loop invariant g >= -2;
  loop assigns g, u;
*/
while (1) {
      if (u>=c) {
          break;
      }
      g = g+2;
      u = u+1;
      g = g*2+5;
  }

}
