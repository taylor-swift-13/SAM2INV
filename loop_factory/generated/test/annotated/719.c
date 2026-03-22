int main1(){
  int ae6, zd9, yy, hyn, j;
  ae6=1*5;
  zd9=0;
  yy=(1%40)+2;
  hyn=0;
  j=zd9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ae6 == 5;
  loop invariant yy > 0;
  loop invariant j >= 0;
  loop invariant hyn >= 0;
  loop assigns hyn, yy, j;
*/
while (yy!=hyn) {
      hyn = yy;
      yy = (yy+ae6/yy)/2;
      j += yy;
  }
}