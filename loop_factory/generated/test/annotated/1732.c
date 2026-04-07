int main1(){
  int jyv, xb, ay;
  jyv=0;
  xb=(1%20)+10;
  ay=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xb + ay + jyv == 20;
  loop invariant 0 <= xb;
  loop invariant 0 <= ay;
  loop invariant 0 <= jyv;
  loop invariant xb == 11 - ((jyv + 1) / 2);
  loop assigns jyv, xb, ay;
*/
for (; xb>0&&ay>0; jyv = jyv + 1) {
      if (!(!(jyv%2==0))) {
          xb = xb - 1;
      }
      else {
          ay = ay - 1;
      }
  }
}