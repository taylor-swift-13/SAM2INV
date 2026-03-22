int main1(){
  int b, cho, i6, t2, waxr;
  b=(1%30)+6;
  cho=b;
  i6=1;
  t2=0;
  waxr=cho;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t2 == (i6-1)*(i6-1);
  loop invariant 1 <= i6;
  loop invariant i6 <= b+1;
  loop invariant waxr == i6 * b;
  loop assigns t2, i6, waxr;
*/
while (i6<=b) {
      t2 = t2+2*i6-1;
      i6 = i6 + 1;
      waxr += b;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t2 == (i6-1)*(i6-1);
  loop invariant i6 == b+1;
  loop invariant ( !(waxr<=t2-1) ) || (waxr + cho - t2 - i6 == 5);
  loop invariant t2 - waxr + b >= 0;
  loop invariant b >= 4;
  loop assigns cho, waxr;
*/
while (1) {
      if (!(waxr<=t2-1)) {
          break;
      }
      cho = t2-waxr;
      waxr = waxr + 5;
      cho = cho + i6;
  }
}