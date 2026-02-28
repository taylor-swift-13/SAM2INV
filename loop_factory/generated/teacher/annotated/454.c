int main1(int n,int q){
  int i, u, h;

  i=n-6;
  u=0;
  h=u;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == n - 6;
  loop invariant u == 0;
  loop invariant h >= 0;
  loop invariant h % 4 == 0;
  loop invariant n == \at(n,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant i == \at(n, Pre) - 6;
  loop invariant 4 + u != 0;
  loop invariant (h - u) % (4 + u) == 0;
  loop assigns h;
*/
while (1) {
      h = h+4;
      h = h+u;
  }

}
