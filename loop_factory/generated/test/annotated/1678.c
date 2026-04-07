int main1(){
  int i6lt, bqv, l8;
  i6lt=1+13;
  bqv=-6;
  l8=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (l8 == 1) || (l8 == 2);
  loop invariant i6lt >= bqv;
  loop invariant i6lt <= 14;
  loop invariant bqv == -6;
  loop invariant (i6lt == 14) || (i6lt == bqv);
  loop invariant ((i6lt - bqv) == 20) || ((i6lt - bqv) == 0);
  loop assigns i6lt, l8;
*/
while (bqv+1<=i6lt) {
      if (l8==1) {
          l8 = 2;
      }
      else {
          if (l8==2) {
              l8 = 1;
          }
      }
      i6lt = (bqv+1)-1;
  }
}