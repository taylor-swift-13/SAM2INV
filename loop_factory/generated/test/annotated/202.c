int main1(){
  int j, ph, i;
  j=(1%36)+18;
  ph=j;
  i=ph;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 19;
  loop invariant ph <= 19;
  loop invariant ph >= 0;
  loop assigns ph;
*/
for (; ph>=1; ph--) {
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i >= j;
  loop assigns j;
*/
while (j+1<=i) {
      j++;
  }
}