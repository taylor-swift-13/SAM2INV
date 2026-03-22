int main1(){
  int j9q, y, ei4, tph1, bq;
  j9q=1;
  y=0;
  ei4=j9q;
  tph1=3;
  bq=(1%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ei4 == tph1 - 2;
  loop invariant (bq >= 0 && bq <= 9);
  loop invariant (y >= 0);
  loop assigns y, tph1, ei4, bq;
*/
while (1) {
      if (!(bq>=1)) {
          break;
      }
      y = y+ei4*ei4;
      tph1 = tph1+bq*bq;
      ei4 = ei4+bq*bq;
      bq -= 1;
      y = y*2+2;
  }
}