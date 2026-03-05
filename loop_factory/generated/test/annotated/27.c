int main1(int h){
  int wb8, d4v;
  wb8=3;
  d4v=-15880;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wb8 == 3;
  loop invariant d4v <= -15880;
  loop invariant h >= \at(h, Pre);
  loop assigns d4v, h;
*/
while (d4v+1<0) {
      d4v = d4v+d4v+3;
      d4v += 2;
      h = h + wb8;
  }
}