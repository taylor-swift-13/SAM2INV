int main1(int a,int k){
  int m, j, v, h, z, c;

  m=a+6;
  j=0;
  v=k;
  h=k;
  z=6;
  c=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant z == 6;
  loop invariant h == k || h == z;
  loop invariant v >= k;
  loop invariant m == a + 6;
  loop invariant h == k || h == 6;

  loop assigns h, v;
*/
while (1) {
      if (z<=h) {
          h = z;
      }
      v = v+1;
  }

}
