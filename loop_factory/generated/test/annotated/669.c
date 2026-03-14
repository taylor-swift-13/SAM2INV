int main1(int j){
  int w, kk, i2, b, o6m, vhj;
  w=j+19;
  kk=0;
  i2=0;
  b=0;
  o6m=kk;
  vhj=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i2 == j*b;
  loop invariant o6m == 2*b;
  loop invariant vhj >= \at(j, Pre) + 19;
  loop invariant 0 <= b;
  loop invariant w == j + 19;
  loop assigns b, i2, o6m, vhj;
*/
while (1) {
      if (!(b<w)) {
          break;
      }
      b += 1;
      i2 += j;
      o6m += 2;
      vhj = vhj+(b%6);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o6m >= 0;
  loop invariant w >= j + 19;
  loop assigns b, i2, o6m, vhj, w;
*/
while (o6m+3<=i2) {
      b = b + w;
      vhj += b;
      w += 2;
      i2 = (o6m+3)-1;
  }
}