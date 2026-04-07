int main1(){
  int rm, gvr, gaz, j2y, yy6z;
  rm=1;
  gvr=0;
  gaz=0;
  j2y=0;
  yy6z=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gaz  == gvr * (gvr + 1) * (gvr + 2) * (gvr + 3) / 24;
  loop invariant 0 <= gvr <= rm;
  loop invariant j2y == gvr*(gvr+1)/2 &&
                   yy6z == gvr*(gvr+1)*(gvr+2)/6 &&
                   gaz  == gvr*(gvr+1)*(gvr+2)*(gvr+3)/24;
  loop invariant (rm == 1);
  loop assigns gvr, j2y, yy6z, gaz;
*/
while (gvr < rm) {
      gvr += 1;
      j2y = j2y + gvr;
      yy6z = yy6z + j2y;
      gaz += yy6z;
  }
}