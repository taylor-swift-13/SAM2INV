int main1(){
  int j7b, wd, i, qbj, saw;
  j7b=1+25;
  wd=4;
  i=0;
  qbj=0;
  saw=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qbj == i*(i+1)/2;
  loop invariant (i == 0) ==> (wd == 4);
  loop invariant (i > 0) ==> (wd == j7b);
  loop invariant 0 <= i;
  loop invariant i <= 1;
  loop invariant i <= j7b - 1;
  loop invariant saw >= 3;
  loop assigns i, qbj, saw, wd;
*/
while (1) {
      if (!(wd<=j7b-1)) {
          break;
      }
      i = i + 1;
      qbj = qbj + i;
      saw = saw + wd;
      wd = j7b;
  }
}