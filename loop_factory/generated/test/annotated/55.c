int main1(int b){
  int iil, tj7j;
  iil=(b%39)+7;
  tj7j=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= tj7j;
  loop invariant b >= \at(b, Pre);
  loop invariant iil == (\at(b, Pre) % 39) + 7;
  loop invariant iil > 0 ==> tj7j <= 2*iil - 1;
  loop assigns b, tj7j;
*/
while (tj7j<iil) {
      tj7j = 2*tj7j;
      tj7j += 1;
      b += iil;
  }
}