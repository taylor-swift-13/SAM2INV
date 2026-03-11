int main1(){
  int j, nw;
  j=1+12;
  nw=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (nw % 3) == (j % 3);
  loop invariant (0 <= nw);
  loop invariant (nw <= j);
  loop invariant (nw % 3 == 1);
  loop invariant (j == 13);
  loop assigns nw;
*/
while (1) {
      if (!(nw>=3)) {
          break;
      }
      nw = nw - 3;
  }
}