int main1(int c,int b){
  int i4i, ggb;
  i4i=38;
  ggb=i4i;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ggb == i4i;
  loop invariant b == \at(b, Pre);
  loop invariant c == \at(c, Pre);
  loop invariant 0 <= ggb;
  loop invariant i4i == 38;
  loop invariant 0 < ggb;
  loop assigns ggb;
*/
while (ggb<i4i&&ggb>0) {
      ggb++;
      ggb -= 1;
  }
}