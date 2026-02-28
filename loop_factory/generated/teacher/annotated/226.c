int main1(int b,int n){
  int k, v, z, s;

  k=21;
  v=0;
  z=k;
  s=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 21;
  loop invariant v == 0;
  loop invariant s == 21;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v <= k;
  loop invariant s == k;
  loop invariant v >= 0;
  loop invariant z >= s;
  loop invariant z % 2 == 1;
  loop invariant z >= 21;
  loop assigns z;
*/
while (v<k) {
      if (v<k/2) {
          z = z+s;
      }
      else {
          z = z*s;
      }
      z = z*2+1;
  }

}
