int main1(int k,int p){
  int d, i, v;

  d=p+3;
  i=2;
  v=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == p + 3;
  loop invariant i % 2 == 0;
  loop invariant v >= -8;
  loop invariant p == \at(p, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant i >= 2;
  loop invariant v <= 2*i - 12;
  loop invariant v >= -8 + 3 * ((i - 2) / 2);
  loop invariant d == \at(p, Pre) + 3;

  loop invariant ((i - 2) % 2) == 0;
  loop assigns v, i;
*/
while (i+2<=d) {
      v = v+1;
      v = v+2;
      if (v+7<d) {
          v = v+1;
      }
      i = i+2;
  }

}
