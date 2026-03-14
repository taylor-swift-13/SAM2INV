int main1(int i,int s){
  int wg5, x, i4a, b96l;
  wg5=i-9;
  x=wg5;
  i4a=-15364;
  b96l=x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == \at(i, Pre) - 9;
  loop invariant b96l == x + 2 * ((i - \at(i, Pre)) / 3);
  loop invariant (i - \at(i, Pre)) >= 0;
  loop invariant ((i - \at(i, Pre)) % 3 == 0);
  loop invariant (i4a + 15364) == ((i - \at(i, Pre))/3) * ( ((i - \at(i, Pre))/3) + \at(i, Pre) - 8 );
  loop invariant s == \at(s,Pre) + ((i - \at(i,Pre))/3) * x;
  loop invariant x == wg5;
  loop assigns i, i4a, b96l, s;
*/
while (1) {
      if (!(i4a+6<0)) {
          break;
      }
      i4a = i4a+b96l+2;
      i = i + 3;
      b96l += 2;
      s += x;
  }
}