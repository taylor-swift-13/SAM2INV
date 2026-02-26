int main1(int n,int p){
  int z, b, v;

  z=n-8;
  b=z;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == n - 8;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant b <= z;
  loop invariant z == \at(n, Pre) - 8;
  loop invariant z >= 0 ==> b >= 0 && b <= z;
  loop assigns b;
*/
while (b>=1) {
      b = b/2;
  }

}
