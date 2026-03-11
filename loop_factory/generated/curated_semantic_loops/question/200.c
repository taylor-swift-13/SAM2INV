int main1(int b){
  int k, j, r;

  k=67;
  j=k;
  r=j;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (j-2>=0) {
      j = j-2;
  }
/*@
  assert !(j-2>=0) &&
         (b == \at(b, Pre));
*/

}
