int main1(){
  int bk, p56, msv;
  bk=1+15;
  p56=4;
  msv=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bk == 16;
  loop invariant p56 == 4;
  loop invariant p56 <= bk - 1;
  loop invariant (msv == 0) || (msv == 2);
  loop assigns msv;
*/
while (p56<=bk-1) {
      if (msv==1) {
          msv = 2;
      }
      else {
          if (msv==2) {
              msv = 1;
          }
      }
      msv = msv + 1;
      msv -= msv;
  }
}