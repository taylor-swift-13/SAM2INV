int main1(){
  int o, putl, qj;
  o=1+20;
  putl=o;
  qj=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == 1 + 20;
  loop invariant putl == o;
  loop invariant qj >= 2;
  loop assigns qj;
*/
while (putl>=1) {
      if (qj==1) {
          qj = 2;
      }
      else {
          if (qj==2) {
              qj = 1;
          }
      }
      qj = qj + qj;
      qj = qj + putl;
  }
}