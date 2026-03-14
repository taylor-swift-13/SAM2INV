int main1(int r){
  int jidk, lc, uds;
  jidk=0;
  lc=(r%20)+10;
  uds=(r%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jidk >= 0;
  loop invariant lc + uds == ((\at(r, Pre) % 20) + 10) + ((\at(r, Pre) % 15) + 8) - jidk;
  loop invariant lc + uds + jidk == (r % 20) + (r % 15) + 18;
  loop assigns jidk, lc, uds;
*/
while (lc>0&&uds>0) {
      if (jidk%2==0) {
          lc--;
      }
      else {
          uds = uds - 1;
      }
      jidk++;
  }
}