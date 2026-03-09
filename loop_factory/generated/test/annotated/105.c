int main1(){
  int awic, d8, rb, m;
  awic=(1%15)+10;
  d8=awic;
  rb=(1%20)+10;
  m=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rb >= 0;
  loop invariant m >= 0;
  loop invariant d8 + rb + m == 31;
  loop invariant d8 >= awic;
  loop assigns rb, m, d8;
*/
while (rb>0&&m>0) {
      if (d8%2==0) {
          rb = rb - 1;
      }
      else {
          m -= 1;
      }
      d8 = d8 + 1;
  }
}