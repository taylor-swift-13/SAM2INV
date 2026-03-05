int main1(){
  int k;
  k=16;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 16;
  loop assigns k;
*/
while (k>0) {
      k += 1;
      k = k - 1;
  }
}