int main1(int r,int g){
  int w, ke, ptuo, yqd;
  w=r*5;
  ke=3;
  ptuo=0;
  yqd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ptuo == yqd * r;
  loop invariant w == 5 * r;
  loop invariant 0 <= yqd;
  loop assigns ptuo, yqd;
*/
while (yqd<w) {
      ptuo += r;
      yqd++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == (ke + 2) * r;
  loop invariant 0 <= yqd;
  loop invariant 0 <= ke;
  loop assigns w, ke;
*/
while (1) {
      if (!(ke<yqd)) {
          break;
      }
      w += r;
      ke++;
  }
}