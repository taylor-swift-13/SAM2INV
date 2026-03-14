int main1(){
  int h4eu, es, ym, fd;
  h4eu=(1%34)+5;
  es=0;
  ym=0;
  fd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ym == es*(es - 1) / 2;
  loop invariant fd == es*(es*es + 5) / 6;
  loop invariant 0 <= es;
  loop invariant es <= h4eu;
  loop assigns es, ym, fd;
*/
while (es<=h4eu-1) {
      ym += es;
      fd += ym;
      es = es + 1;
      fd++;
  }
}