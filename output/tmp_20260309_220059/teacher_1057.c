int main1(int b,int k){
  int z, j, v, c;

  z=40;
  j=0;
  v=k;
  c=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == 40;
  loop invariant c == \at(b, Pre);
  loop invariant 0 <= j && j <= z;
  loop invariant b == \at(b, Pre) && k == \at(k, Pre);
  loop invariant v == \at(k, Pre) + j*(3 + c) && j >= 0 && j <= z;
  loop invariant c == \at(b, Pre) && z == 40 && k == \at(k, Pre) && b == \at(b, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant c == b;
  loop invariant c == \at(b, Pre) && z == 40 && 0 <= j && j <= z;
  loop invariant v == \at(k, Pre) + j*(3 + c) && b == \at(b, Pre) && k == \at(k, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant 0 <= j && j <= z && c == \at(b, Pre) && z == 40;
  loop invariant v == \at(k, Pre) + j*(3 + c) && 0 <= j && j <= z;
  loop invariant c == \at(b, Pre) && k == \at(k, Pre) && z == 40;
  loop assigns j, v;
*/
while (1) {
      if (j>=z) {
          break;
      }
      v = v+3;
      j = j+1;
      v = v+c;
  }
/*@
  assert (z == 40) &&
         (j == z) &&
         (c == \at(b, Pre)) &&
         (v == \at(k, Pre) + z * (3 + c));
*/

}
