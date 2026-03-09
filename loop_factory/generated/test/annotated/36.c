int main1(){
  int r7f, dr1, hz8, h3f;
  r7f=1-1;
  dr1=r7f;
  hz8=dr1;
  h3f=dr1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r7f == 0;
  loop invariant dr1 >= 0;
  loop invariant hz8 == 2*dr1;
  loop invariant h3f == dr1*(dr1+2);
  loop assigns dr1, hz8, h3f;
*/
while (dr1-1>=0) {
      hz8 = hz8 + 1;
      h3f += 1;
      hz8 = hz8 + 1;
      h3f = (hz8)+(h3f);
      if (hz8<dr1+2) {
          hz8 = hz8 + h3f;
      }
      dr1 += 1;
  }
}