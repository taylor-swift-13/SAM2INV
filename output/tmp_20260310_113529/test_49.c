int main1(int i){
  int zr0a, xsp, es2l, o9a;
  zr0a=(i%21)+19;
  xsp=0;
  es2l=0;
  o9a=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o9a + xsp == 8;
  loop invariant i == \at(i, Pre) + xsp*(xsp+1)/2;
  loop invariant 0 <= xsp;
  loop invariant 0 <= o9a;
  loop invariant es2l >= 0;
  loop invariant 2*es2l == xsp*(17 - xsp);
  loop assigns xsp, es2l, o9a, i;
*/
while (1) {
      if (!(xsp<zr0a&&o9a>0)) {
          break;
      }
      xsp += 1;
      es2l = es2l + o9a;
      o9a -= 1;
      i = i + xsp;
  }
}