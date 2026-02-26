int main1(int a,int m){
  int t, x, q, u;

  t=48;
  x=t;
  q=5;
  u=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == 5;
  loop invariant t == 48;
  loop invariant m == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant 0 <= x;
  loop invariant x <= t;
  loop invariant x >= 0;
  loop invariant x <= 48;
  loop invariant x < 48 ==> (u - q) % 2 == 0;
  loop assigns u, x;
*/
while (x>0) {
      u = u+u;
      u = u+q;
      x = x-1;
  }

}
