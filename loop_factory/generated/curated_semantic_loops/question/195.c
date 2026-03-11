int main1(int b,int n){
  int z, h, d;

  z=(b%37)+4;
  h=z;
  d=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (h-2>=0) {
      d = d+4;
      if (h+6<=n+z) {
          d = d-d;
      }
      else {
          d = d+1;
      }
  }
/*@
  assert !(h-2>=0) &&
         (b == \at(b, Pre));
*/

}
