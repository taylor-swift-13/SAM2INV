int main1(){
  int uyg;
  uyg=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant uyg * (uyg - 1) == 0;
  loop assigns uyg;
*/
while (uyg!=uyg) {
      if (uyg>uyg) {
          uyg = uyg - uyg;
          uyg = uyg - uyg;
          uyg = uyg - uyg;
      }
      else {
          uyg = uyg - uyg;
          uyg = uyg - uyg;
          uyg = uyg - uyg;
      }
  }
}