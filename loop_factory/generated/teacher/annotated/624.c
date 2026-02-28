int main1(int k,int n){
  int v, z, s, y;

  v=k+4;
  z=v;
  s=z;
  y=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z <= v;
  loop invariant s >= z;
  loop invariant (s - z) % 4 == 0;
  loop invariant v == k + 4;
  loop invariant s == 5*z - 4*v;
  loop invariant k == \at(k, Pre);
  loop invariant v == \at(k, Pre) + 4;
  loop assigns s, z;
*/
while (1) {
      if (z>=v) {
          break;
      }
      s = s+3;
      z = z+1;
      s = s+2;
  }

}
