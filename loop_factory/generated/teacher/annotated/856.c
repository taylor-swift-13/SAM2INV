int main1(int m,int n){
  int i, u, r;

  i=m-10;
  u=3;
  r=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == m - 10;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant u >= 3;
  loop invariant (r == n) || (r >= 0);
  loop invariant r == n || r >= 0;
  loop invariant r*r >= r;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre) && u >= 3;
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant n == 0 ==> r == 0;
  loop invariant i == \at(m, Pre) - 10;
  loop invariant r >= n;
  loop assigns r, u;
*/
while (1) {
      r = r*r;
      u = u+1;
  }

}
