int main1(int q,int w){
  int g, go, mr;
  g=0;
  go=(w%20)+10;
  mr=(w%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant go + mr + g == ((\at(w,Pre) % 20) + 10) + ((\at(w,Pre) % 15) + 8);
  loop invariant go == ((w % 20) + 10) - ((g + 1) / 2);
  loop invariant mr == ((w % 15) + 8) - (g / 2);
  loop invariant 0 <= g;
  loop invariant go + mr ==
      ((\at(w,Pre) % 20) + 10) + ((\at(w,Pre) % 15) + 8) - g;
  loop invariant go == ((\at(w, Pre) % 20) + 10) - ((g + 1) / 2);
  loop invariant mr == ((\at(w, Pre) % 15) + 8) - (g / 2);
  loop assigns g, go, mr;
*/
for (; go>0&&mr>0; g++) {
      if (!(!(g%2==0))) {
          go -= 1;
      }
      else {
          mr -= 1;
      }
  }
/*@
  assert g >= 0;
  assert (go <= 0 || mr <= 0);
  assert go == ((\at(w, Pre) % 20) + 10) - (g + 1) / 2;
  assert mr == ((\at(w, Pre) % 15) + 8) - g / 2;
*/
}
