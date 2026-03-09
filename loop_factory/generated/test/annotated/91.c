int main1(int d){
  int o, w, zi1;
  o=d*2;
  w=0;
  zi1=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == (\at(d, Pre) + (zi1*(zi1+1))/2);
  loop invariant o == (2 * \at(d, Pre));
  loop invariant w == (zi1 % 8);
  loop invariant 0 <= zi1;
  loop assigns d, w, zi1;
*/
while (zi1<=o-1) {
      w = (w+1)%8;
      zi1 = zi1 + 1;
      d += zi1;
  }
}