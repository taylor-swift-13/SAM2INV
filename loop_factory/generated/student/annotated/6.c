int main1(int k,int p){
  int h, a, d;

  h=k;
  a=0;
  d=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == \at(k, Pre) + 3 * (d - \at(k, Pre)) / 3;
  loop invariant h == \at(k, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);


  loop assigns d;
*/
while (1) {
      d = d+3;
  }

}
