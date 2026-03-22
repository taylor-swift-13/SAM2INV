int main1(){
  int z00w, k0q, mt, pue, r, v7;
  z00w=1+17;
  k0q=0;
  mt=(1%28)+8;
  pue=(1%22)+5;
  r=0;
  v7=z00w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pue == 2*(pue/2) + (pue%2);
  loop invariant z00w == 18;
  loop invariant k0q == 0;
  loop invariant v7 == z00w;
  loop invariant mt > 0;
  loop invariant r >= 0;
  loop invariant 0 <= pue <= 6;
  loop invariant r + pue * mt == 54;
  loop assigns r, mt, pue, v7;
*/
while (1) {
      if (!(pue!=0)) {
          break;
      }
      if (pue%2==1) {
          r = r + mt;
          pue--;
      }
      mt = 2*mt;
      v7 += k0q;
      pue = pue/2;
  }
}