int main1(){
  int zu, q6, ytz, zg;
  zu=(1%28)+18;
  q6=0;
  ytz=zu;
  zg=zu;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= q6 <= zu;
  loop invariant ytz >= zu;
  loop invariant (q6 == 0) ==> (ytz == zu);
  loop invariant zg == zu;
  loop assigns ytz, q6;
*/
while (1) {
      if (!(q6<zu)) {
          break;
      }
      if (!(!(q6<zu/2))) {
          ytz += 1;
      }
      else {
          ytz = ytz + zg;
      }
      q6 = zu;
  }
}