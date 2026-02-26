int main1(int a,int m){
  int t, x, q, u;

  t=48;
  x=0;
  q=-4;
  u=x;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == 48;
  loop invariant u == 0;
  loop invariant 0 <= x;
  loop invariant x <= t;
  loop invariant q - x == -4;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant q == x - 4;
  loop invariant x >= 0;
  loop assigns q, x;
*/
while (x<=t-1) {
      q = q+u+u;
      q = q+1;
      x = x+1;
  }

}
