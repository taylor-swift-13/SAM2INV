int main1(int a){
  int mrz, xbr, zu;
  mrz=a;
  xbr=1;
  zu=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a,Pre) + zu*(zu+1)/2;
  loop invariant 0 <= zu;
  loop invariant xbr >= 1;
  loop assigns a, zu, xbr;
*/
while (xbr<=mrz) {
      zu = (1)+(zu);
      xbr = 2*xbr;
      a = a + zu;
  }
}