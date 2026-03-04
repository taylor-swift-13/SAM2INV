int main1(int b,int s){
  int zcw, i9, h;
  zcw=(b%26)+5;
  i9=0;
  h=zcw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == zcw - i9;
  loop invariant b == \at(b, Pre) + i9;
  loop invariant zcw == (\at(b, Pre) % 26) + 5;
  loop invariant i9 >= 0;
  loop invariant 0 <= i9;
  loop invariant s == \at(s, Pre) + i9*(zcw - 1) - ((i9*(i9 - 1))/2);
  loop assigns i9, h, s, b;
*/
while (1) {
      if (!(i9<zcw&&h>0)) {
          break;
      }
      i9 = i9 + 1;
      h = h - 1;
      s += h;
      b += 1;
  }
}