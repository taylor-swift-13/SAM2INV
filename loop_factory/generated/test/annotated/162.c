int main1(){
  int epa;
  epa=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant epa == 0 || epa == 1;
  loop assigns epa;
*/
while (epa!=epa) {
      if (epa>epa) {
          epa -= epa;
          epa -= epa;
          epa -= epa;
      }
      else {
          epa -= epa;
          epa -= epa;
          epa -= epa;
      }
      epa = epa*2;
  }
}