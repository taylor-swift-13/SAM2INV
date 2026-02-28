int main1(int a,int k){
  int f, v, z, g, m, i;

  f=a+4;
  v=0;
  z=v;
  g=f;
  m=k;
  i=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == k;
  loop invariant z >= 0;
  loop invariant g <= a + 4;
  loop invariant (g >= a + 4) || (g >= k);
  loop invariant f == a + 4;

  loop invariant (a + 4 <= m) ==> (g == a + 4);

  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (a+4 <= k) ==> (g >= a+4);
  loop invariant (a+4 > k) ==> (g >= k);
  loop assigns g, z;
*/
while (1) {
      if (m<=g) {
          g = m;
      }
      z = z+1;
  }

}
