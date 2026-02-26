int main1(int a,int m){
  int t, x, q, u;

  t=48;
  x=t;
  q=5;
  u=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x > 0;
  loop invariant q >= 5;
  loop invariant u >= m;
  loop invariant m == \at(m, Pre);
  loop invariant u - m >= 3*(q - 5);
  loop invariant x >= 0;
  loop invariant x <= 48;
  loop invariant a == \at(a, Pre);
  loop invariant (q - 5) % 3 == 0;
  loop invariant q % 3 == 2;
  loop invariant (u - m) % 3 == 0;
  loop invariant x == 48;
  loop invariant u == m + ((q - 5) * (q + 10)) / 6;
  loop assigns q, u;
*/
while (x>0) {
      q = q+1;
      u = u+1;
      q = q+2;
      u = u+q;
  }

}
