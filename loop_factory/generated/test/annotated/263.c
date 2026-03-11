int main1(int v,int p){
  int t, gn, z8ez, l, ru;
  t=v+22;
  gn=0;
  z8ez=0;
  l=0;
  ru=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gn == ru;
  loop invariant l == ru % 12;
  loop invariant z8ez == ru / 12;
  loop invariant t == v + 22;
  loop invariant 0 <= gn;
  loop assigns gn, l, ru, z8ez;
*/
while (1) {
      if (!(gn<t)) {
          break;
      }
      ru = ru + 1;
      l = l + 1;
      if (l>=12) {
          l = l - 12;
          z8ez += 1;
      }
      gn = gn + 1;
  }
}