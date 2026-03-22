int main1(int r,int k){
  int mxp, pk2, km;
  mxp=50;
  pk2=0;
  km=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mxp == 50;
  loop invariant r - \at(r,Pre) >= 5 * pk2;
  loop invariant 0 <= pk2 <= mxp;
  loop invariant (pk2 <= mxp/2) ==> (km == 5);
  loop invariant (pk2 >= mxp/2) ==> (km == 5 + 2*(pk2 - mxp/2));
  loop assigns r, pk2, km;
*/
while (pk2<=mxp-1) {
      if (pk2>=mxp/2) {
          km += 2;
      }
      r += km;
      pk2 += 1;
  }
}