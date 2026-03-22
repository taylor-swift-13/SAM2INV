int main1(int i,int s){
  int h, i41, d6b7, bx;
  h=i+12;
  i41=0;
  d6b7=-5;
  bx=h;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i, Pre);
  loop invariant h == i + 12;
  loop invariant i41 >= 0;
  loop assigns i41;
*/
for (; i41<=h-1; i41 += 1) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i - h*bx == \at(i, Pre) - (\at(i, Pre) + 12) * bx;
  loop assigns i, h, i41;
*/
while (h<=d6b7) {
      i41 = i41+2*h-1;
      h += 1;
      i += bx;
  }
}