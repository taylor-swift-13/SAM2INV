int main1(int a,int b){
  int n, u, k, v;

  n=67;
  u=n+4;
  k=1;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u <= n + 4;
  loop invariant n == 67;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);

  loop invariant u >= 1;
  loop assigns u;
*/
while (u>1) {
      u = u/2;
  }

}
