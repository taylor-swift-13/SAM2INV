int main1(int k,int n){
  int j, u, v;

  j=k;
  u=0;
  v=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*(v - j) == u*(u+1);
  loop invariant u >= 0;
  loop invariant v >= j;
  loop invariant j == \at(k, Pre);
  loop invariant k == \at(k, Pre) && n == \at(n, Pre);
  loop invariant u >= 0 && v >= j;
  loop invariant k == \at(k, Pre) && n == \at(n, Pre) && j == \at(k, Pre) && u >= 0;
  loop invariant 2 * (v - j) == u * (u + 1);
  loop invariant 2*v == 2*j + u*(u+1);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 2*(v - j) == u*(u+1) && u >= 0;
  loop invariant v >= j && j == k && k == \at(k, Pre);
  loop invariant v - u*(u+1)/2 == j;
  loop invariant v == j + u*(u+1)/2;
  loop invariant j == \at(k,Pre);
  loop invariant 2*(v - j) == u*u + u;
  loop assigns u, v;
*/
while (1) {
      v = v+u;
      v = v+1;
      u = u+1;
  }

}
