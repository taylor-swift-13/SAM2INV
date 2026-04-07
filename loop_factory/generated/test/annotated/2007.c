int main1(int l){
  int j, gl80, kbp, j3a, bb;
  j=134;
  gl80=0;
  kbp=j;
  j3a=j;
  bb=gl80;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j3a == j - gl80;
  loop invariant bb == j * gl80 - (gl80 * (gl80 + 1)) / 2;
  loop invariant (gl80 == 0 ==> kbp == j3a) && (gl80 > 0 ==> kbp == j3a + 1);
  loop invariant (0 <= gl80 && gl80 <= j);
  loop assigns bb, gl80, j3a, kbp;
*/
while (1) {
      if (!(gl80 < j)) {
          break;
      }
      gl80 = gl80 + 1;
      kbp = j3a;
      j3a = j - gl80;
      bb += j3a;
  }
}