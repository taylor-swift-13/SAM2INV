int main1(int l){
  int fs, ubz9, ww, au, q;
  fs=172;
  ubz9=fs;
  ww=0;
  au=fs;
  q=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == ww * (ubz9 + 1);
  loop invariant au == fs - ww;
  loop invariant ubz9 == fs;
  loop invariant ww >= 0;
  loop invariant fs == 172;
  loop assigns q, ww, au;
*/
while (1) {
      if (!(ww<fs&&au>0)) {
          break;
      }
      q += ubz9;
      ww++;
      au -= 1;
      q += 1;
  }
}