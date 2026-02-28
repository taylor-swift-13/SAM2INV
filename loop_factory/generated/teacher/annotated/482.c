int main1(int m,int n){
  int j, k, t, c;

  j=n;
  k=0;
  t=k;
  c=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == n;
  loop invariant (t + 5*c) == 10;
  loop invariant t >= 0;
  loop invariant c <= 2;
  loop invariant t + 5*c == 10;
  loop invariant j == \at(n, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant t == 5 * (2 - c);
  loop invariant n == \at(n, Pre);
  loop assigns t, c;
*/
while (1) {
      t = t+4;
      t = t+1;
      c = c-1;
  }

}
