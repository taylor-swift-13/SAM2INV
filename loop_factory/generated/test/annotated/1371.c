int main1(int w){
  int ska, l2l, gd;
  ska=w;
  l2l=ska+3;
  gd=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l2l >= ska;
  loop invariant (((l2l - ska) % 3) == 0);
  loop invariant ska == w;
  loop invariant (gd % 2) == 0;
  loop invariant (gd >= 2);
  loop invariant (l2l <= ska + 3);
  loop assigns gd, l2l;
*/
while (l2l>=ska+1) {
      gd = gd*2;
      l2l = l2l - 3;
  }
}