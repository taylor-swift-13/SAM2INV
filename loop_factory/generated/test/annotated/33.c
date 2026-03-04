int main1(int c,int j,int e){
  int k, ny0n, zto;
  k=c-8;
  ny0n=0;
  zto=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ny0n >= 0;
  loop invariant zto == \at(e, Pre) + ny0n;
  loop invariant c == \at(c, Pre) + 2 * ny0n;
  loop invariant j == \at(j, Pre) + ny0n * (\at(e, Pre) + 1) + ny0n * (ny0n - 1) / 2;
  loop invariant e == \at(e, Pre);
  loop invariant j == \at(j, Pre) + ny0n * \at(e, Pre) + ny0n*(ny0n+1)/2;
  loop invariant zto - ny0n == e;
  loop invariant j == \at(j,Pre) + ny0n*(e + 1) + ny0n*(ny0n - 1)/2;
  loop invariant ny0n <= k || k < 0;
  loop invariant zto == e + ny0n;
  loop invariant j == \at(j, Pre) + ny0n*e + ny0n*(ny0n+1)/2;
  loop invariant k == \at(c, Pre) - 8;
  loop invariant 0 <= ny0n;
  loop assigns c, j, ny0n, zto;
*/
while (ny0n<k) {
      zto++;
      ny0n += 1;
      c += 2;
      j = j + zto;
  }
}