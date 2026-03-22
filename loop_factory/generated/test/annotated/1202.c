int main1(){
  int kog, zzhg, uv5, truw;
  kog=0;
  zzhg=0;
  uv5=(1%50)+20;
  truw=(1%8)+2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant truw >= zzhg + 1;
  loop invariant 0 <= zzhg;
  loop invariant 0 <= uv5 <= 21;
  loop invariant truw - kog >= 2;
  loop invariant kog >= 0;
  loop assigns kog, zzhg, uv5, truw;
*/
while (uv5!=0) {
      if (zzhg+1==truw) {
          kog = kog + 1;
          zzhg = 0;
      }
      else {
          zzhg++;
      }
      uv5--;
      truw = truw + kog;
  }
}