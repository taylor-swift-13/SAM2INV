int main1(int h,int j){
  int o, kmz, liu, b56;
  o=h+15;
  kmz=0;
  liu=1;
  b56=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((h - \at(h,Pre)) == 0) || ((h - \at(h,Pre)) == o);
  loop invariant (b56 - liu) == (j - 1);
  loop invariant o == \at(h,Pre) + 15;
  loop invariant (kmz == 0) ==> (h == \at(h, Pre));
  loop invariant (kmz == 0) ==> (b56 == j);
  loop invariant (kmz == 0) ==> (liu == 1);
  loop invariant (kmz != 0) ==> (b56 == j + 3);
  loop invariant (kmz == 0) || (kmz == o);
  loop assigns b56, liu, h, kmz;
*/
while (1) {
      if (!(kmz<o)) {
          break;
      }
      b56 = (3)+(b56);
      liu = liu + 3;
      h = h + o;
      kmz = o;
  }
}