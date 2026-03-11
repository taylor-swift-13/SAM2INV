int main1(int z,int b){
  int si, r, n, v4x;
  si=z+25;
  r=0;
  n=0;
  v4x=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == v4x * z;
  loop invariant b == \at(b, Pre) + v4x * r;
  loop invariant si == \at(z, Pre) + 25;
  loop invariant v4x >= 0;
  loop invariant z == \at(z,Pre);
  loop assigns n, b, v4x;
*/
while (1) {
      if (!(v4x<si)) {
          break;
      }
      n += z;
      b += r;
      v4x += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == \at(z, Pre) + (v4x - si) * r;
  loop invariant n == v4x * (si - 25) + r * (v4x - si) * (v4x - si - 1) / 2;
  loop invariant si == \at(z, Pre) + 25;
  loop invariant v4x >= 0;
  loop invariant z == \at(z,Pre);
  loop assigns v4x, n, z;
*/
while (v4x<si) {
      v4x += 1;
      n += z;
      z += r;
  }
}