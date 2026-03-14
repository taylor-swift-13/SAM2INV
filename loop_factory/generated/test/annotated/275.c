int main1(int z){
  int mbr, k, ba, gh9, kw, ka;
  mbr=z;
  k=mbr;
  ba=41;
  gh9=0;
  kw=1;
  ka=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kw == 1 + (k - mbr);
  loop invariant mbr == z;
  loop invariant ba >= 0;
  loop invariant gh9 >= 0;
  loop invariant ka >= 0;
  loop invariant kw >= 1;
  loop invariant gh9 + ba == 41;
  loop assigns ka, k, gh9, ba, kw;
*/
while (ba>0&&k<mbr) {
      if (ba<=kw) {
          ka = ba;
      }
      else {
          ka = kw;
      }
      k += 1;
      gh9 += ka;
      ba -= ka;
      kw++;
  }
}