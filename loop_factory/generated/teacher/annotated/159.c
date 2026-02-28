int main1(int n){
  int r, j, v;

  r=n;
  j=4;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 4;
  loop invariant r == \at(n, Pre);
  loop invariant j <= r || r < 4;
  loop invariant v <= \at(n, Pre) + (j - 4);
  loop invariant n == \at(n, Pre);
  loop invariant j <= r || j == 4;
  loop invariant ( \at(n, Pre) >= 0 ==> v <= \at(n, Pre) + (j - 4) )
                   && ( \at(n, Pre) < 0  ==> v <= j - 4 );

  loop invariant 0 <= j % 9;
  loop invariant j % 9 < 9;
  loop assigns v, j;
*/
while (j<r) {
      if ((j%9)==0) {
          v = v-v;
      }
      else {
          v = v+1;
      }
      j = j+1;
  }

}
