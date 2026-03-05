int main1(){
  int h, ihu, ae;
  h=1;
  ihu=h;
  ae=ihu;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == ihu;
  loop invariant ae >= 1;
  loop invariant ihu == 1;
  loop invariant (ae == 1) || (ae % 2 == 0);
  loop assigns ae;
*/
while (ihu>=2) {
      ae += 2;
      ae += ae;
  }
}