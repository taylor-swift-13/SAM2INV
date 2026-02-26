int main1(int a,int m){
  int t, x, q, u;

  t=48;
  x=0;
  q=-4;
  u=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 48;
  loop invariant x <= t;
  loop invariant q == 4*x - 4;
  loop invariant u == 2*x*(x - 1);
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == 4*(x - 1);
  loop invariant 0 <= x;
  loop invariant u == 2*(x-1)*x;
  loop invariant x >= 0;
  loop assigns q, x, u;
*/
while (1) {
      if (x>=t) {
          break;
      }
      q = q+2;
      x = x+1;
      q = q+2;
      u = u+q;
  }

}
