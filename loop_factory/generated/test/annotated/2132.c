int main1(int v){
  int i6e, i4, mb, x;
  i6e=v;
  i4=0;
  mb=v;
  x=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i6e == \at(v, Pre);
  loop invariant i4 >= 0;
  loop invariant mb == \at(v, Pre) + i4;
  loop invariant v == \at(v, Pre) + i4;
  loop invariant x == \at(v, Pre) + 2 * i4;
  loop invariant (\at(v, Pre) > 0) ==> (i4 <= i6e);
  loop assigns mb, v, x, i4;
*/
while (1) {
      if (!(i4 < i6e)) {
          break;
      }
      mb = mb + 1;
      v++;
      x += 2;
      i4++;
  }
}