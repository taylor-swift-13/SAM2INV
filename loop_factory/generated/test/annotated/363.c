int main1(){
  int i9, uwi, bp, ds, ju, i2, mqh;
  i9=30;
  uwi=0;
  bp=0;
  ds=(1%28)+10;
  ju=uwi;
  i2=5;
  mqh=uwi;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ds == 11 - (bp*(bp - 1))/2;
  loop invariant mqh == bp*(bp + 1)/2;
  loop invariant ju == 0;
  loop invariant (bp <= 5);
  loop invariant i9 == 30;
  loop invariant i2 >= 5;
  loop invariant bp >= 0;
  loop assigns ds, bp, i2, ju, mqh;
*/
while (1) {
      if (!(ds>bp)) {
          break;
      }
      ds -= bp;
      bp = bp + 1;
      i2 = i2*i2;
      ju = ju + uwi;
      mqh += bp;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i2 >= 0;
  loop invariant i9 - ju == 30;
  loop invariant ju >= 0;
  loop invariant mqh >= 0;
  loop invariant bp >= 0;
  loop assigns i2, ju, i9, mqh, bp;
*/
while (1) {
      if (!(i2>=1)) {
          break;
      }
      i2 = i2 - 1;
      ju = ju+1*1;
      i9 = i9+1*1;
      mqh = mqh+1*1;
      bp = bp*2+(ju%6)+3;
  }
}