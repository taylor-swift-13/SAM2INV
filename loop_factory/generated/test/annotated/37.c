int main1(){
  int hu6, j, d4;
  hu6=(1%11)+17;
  j=0;
  d4=hu6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hu6 == (1%11)+17;
  loop invariant j == 0;
  loop invariant d4 >= hu6;
  loop invariant d4 % 6 == 0;
  loop assigns j, d4;
*/
while (j+1<=hu6) {
      d4 = d4 + 3;
      d4 += d4;
  }
}