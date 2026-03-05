int main1(){
  int ukt, dr;
  ukt=(1%28)+9;
  dr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dr >= 0;
  loop invariant dr < 2*ukt;
  loop assigns dr;
*/
while (dr<ukt) {
      dr = 2*dr;
      dr++;
  }
}