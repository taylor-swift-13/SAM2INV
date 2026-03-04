int main1(){
  int d7i, l, bnq, iyy;
  d7i=1+10;
  l=0;
  bnq=d7i;
  iyy=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bnq == d7i + l;
  loop invariant iyy == l*(l+1)/2;
  loop invariant 0 <= l <= d7i;
  loop invariant l <= d7i;
  loop invariant l >= 0;
  loop assigns bnq, l, iyy;
*/
while (l<d7i) {
      bnq = bnq + 1;
      l = l + 1;
      iyy += l;
  }
}