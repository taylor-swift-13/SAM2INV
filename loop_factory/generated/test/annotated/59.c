int main1(int q){
  int z, nc, wa, xv;
  z=q;
  nc=0;
  wa=0;
  xv=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == \at(q, Pre);
  loop invariant xv == 6 - nc;
  loop invariant q == \at(q, Pre) + nc*(nc+1)/2;
  loop invariant wa == 6*nc - nc*(nc-1)/2;
  loop assigns nc, wa, q, xv;
*/
while (nc<z&&xv>0) {
      nc += 1;
      wa += xv;
      q = q + nc;
      xv -= 1;
  }
}