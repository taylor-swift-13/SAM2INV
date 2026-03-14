int main1(){
  int vx, n, u4, a, u;
  vx=1;
  n=3;
  u4=1;
  a=0;
  u=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u4 == (1 << a);
  loop invariant u == 3 + 2*a;
  loop invariant a >= 0;
  loop invariant u == 3 + (vx + 1) * a;
  loop invariant u4 >= 1;
  loop invariant u - 2*a == 3;
  loop invariant vx == 1;
  loop assigns a, u, u4;
*/
while (1) {
      if (!(u4<=vx-1)) {
          break;
      }
      u += vx;
      a++;
      u4 = 2*u4;
      u = u + 1;
  }
}