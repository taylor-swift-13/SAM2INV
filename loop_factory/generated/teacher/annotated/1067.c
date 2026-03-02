int main1(int k,int n){
  int h, d, v, i;

  h=40;
  d=0;
  v=-1;
  i=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - 4*i == -21;
  loop invariant i >= 5;
  loop invariant i % 2 == 1;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v - 4*i == -21 && i >= 5 && v >= -1;
  loop invariant v == 4*i - 21;
  loop invariant (i - 5) % 2 == 0;
  loop invariant k == \at(k, Pre) && n == \at(n, Pre);
  loop invariant h == 40;
  loop invariant v + 1 == 4*(i - 5);
  loop assigns v, i;
*/
while (1) {
      v = v+3;
      v = v+5;
      i = i+2;
  }

}
