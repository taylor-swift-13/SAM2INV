int main1(int a,int k,int n,int q){
  int y, d, z;

  y=k-8;
  d=0;
  z=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == \at(k, Pre) - 8;
  loop invariant k == \at(k, Pre);
  loop invariant z % 2 == 0;
  loop invariant z >= 2;
  loop invariant z % 8 == 2;
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant y == k - 8;
  loop assigns z;
*/
while (1) {
      z = z+3;
      z = z+z;
  }

}
