int main1(int z){
  int ouw, tg, r, ob, hv, f;
  ouw=z+5;
  tg=0;
  r=0;
  ob=1;
  hv=1;
  f=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hv == 2*r + 1;
  loop invariant ob == (r + 1) * (r + 1);
  loop invariant ouw == z + 5;
  loop invariant tg == 0;
  loop invariant r >= 0;
  loop invariant f >= 6;
  loop assigns r, hv, ob, f;
*/
while (1) {
      if (!(ob<=ouw)) {
          break;
      }
      r = r + 1;
      hv += 2;
      f = f+(r%7);
      ob += hv;
      f = f + tg;
  }
}