int main1(int v){
  int dc, h, mca2, si;
  dc=v-5;
  h=0;
  mca2=0;
  si=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant si == 3 - h;
  loop invariant mca2 == h * (7 - h) / 2;
  loop invariant 0 <= h <= 3;
  loop assigns mca2, h, si;
*/
while (h<dc&&si>0) {
      mca2 += si;
      h += 1;
      si -= 1;
  }
}