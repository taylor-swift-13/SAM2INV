int main1(int p,int e){
  int ag8, lhqq, gia, dwo4;
  ag8=162;
  lhqq=0;
  gia=4;
  dwo4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dwo4 == gia * lhqq;
  loop invariant ag8 >= lhqq;
  loop invariant dwo4 == 0;
  loop invariant 0 <= lhqq;
  loop invariant ag8 <= 162;
  loop assigns ag8, dwo4;
*/
while (1) {
      if (!(lhqq+1<=ag8)) {
          break;
      }
      dwo4 = dwo4+gia*lhqq;
      ag8 = ((lhqq+1))+(-(1));
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dwo4 == 0;
  loop invariant ag8 >= 0;
  loop invariant ag8 <= 1;
  loop assigns ag8;
*/
while (1) {
      ag8++;
      if (ag8>=dwo4) {
          break;
      }
  }
}