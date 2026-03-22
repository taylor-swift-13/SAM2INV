int main1(int h,int e){
  int gyv, we62, lq, oh, xb, uz;
  gyv=36;
  we62=gyv;
  lq=we62;
  oh=0;
  xb=0;
  uz=we62;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gyv == 36;
  loop invariant e - gyv * uz == \at(e, Pre) - 1296;
  loop invariant lq == 36;
  loop invariant oh == 0;
  loop invariant xb == 2*(uz - 36);
  loop invariant (uz >= 36);
  loop assigns e, lq, oh, uz, xb;
*/
while (1) {
      if (uz>gyv) {
          break;
      }
      lq = lq + oh;
      oh += xb;
      e += gyv;
      uz += 1;
      xb += 2;
  }
}